// Lean compiler output
// Module: Lean.Elab.Structure
// Imports: Init Lean.Parser.Command Lean.Meta.Closure Lean.Meta.SizeOf Lean.Meta.Injective Lean.Elab.Command Lean.Elab.DeclModifiers Lean.Elab.DeclUtil Lean.Elab.Inductive Lean.Elab.DeclarationRange
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedStructFieldInfo;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object**);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3;
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3;
lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkResultUniverse(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__4;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2;
extern lean_object* l_Lean_Elab_instInhabitedAttribute;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__5(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_projections(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2;
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2;
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType_match__1(lean_object*);
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2;
lean_object* l_Lean_Elab_Term_getLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1;
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__10;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1;
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1;
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse_match__1(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2;
uint8_t l_Lean_Elab_Command_StructFieldInfo_inferMod___default;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8;
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4;
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop(lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5;
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1;
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1;
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1;
static uint64_t l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3;
static lean_object* l_Lean_Elab_Command_elabStructure___closed__9;
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__4___boxed(lean_object**);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21;
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4;
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__3(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2;
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_value_x3f___default;
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t, size_t, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2;
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2;
static uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__2;
lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1;
lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___boxed(lean_object**);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1;
static lean_object* l_Lean_Elab_Command_elabStructure___closed__5;
extern lean_object* l_Lean_docStringExt;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3;
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults_match__1(lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView_match__1(lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1;
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__3;
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5;
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14;
uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue_match__1(lean_object*);
lean_object* l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1;
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1;
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18;
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__6;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1;
lean_object* l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4;
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__2;
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabStructure___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4(lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__3;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__1(lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2(lean_object*);
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4;
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2;
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_set_reducibility_status(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Structure___hyg_5182_(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_234_(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections_match__1(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1;
lean_object* l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__2(lean_object*);
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1(lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabLetDeclCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__2(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Command_elabStructure___closed__7;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9(lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6;
lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2(lean_object*);
static lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_instInhabitedStructFieldKind;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfConstant___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1;
static lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1;
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
static uint8_t _init_l_Lean_Elab_Command_instInhabitedStructFieldKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Command_StructFieldInfo_inferMod___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_StructFieldInfo_value_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint64_t _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Elab_Command_StructFieldInfo_isFromParent_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Elab_Command_StructFieldInfo_isSubobject_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_StructFieldInfo_isSubobject(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2;
return x_1;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_12);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2___boxed), 4, 1);
lean_closure_set(x_17, 0, x_12);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3___boxed), 6, 3);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4___boxed), 6, 3);
lean_closure_set(x_19, 0, x_12);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = x_20;
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_7, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_12);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_22);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_st_ref_take(x_7, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_39);
x_45 = lean_st_ref_set(x_7, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_List_reverse___rarg(x_47);
x_49 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_6);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_37);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_6);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec(x_36);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6(x_67, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_67);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_2);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg(x_30);
return x_72;
}
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute [");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_isAttribute(x_14, x_3);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_3);
x_17 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1(x_1, x_3, x_2, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_4);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2;
x_2 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Attr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4;
x_2 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6;
x_2 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_expandMacros), 3, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_6);
lean_inc(x_2);
x_18 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabLetDeclCore___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_Syntax_getKind(x_19);
x_22 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = lean_name_mk_string(x_25, x_24);
x_27 = lean_unbox(x_13);
lean_dec(x_13);
x_28 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2(x_27, x_19, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_13);
x_29 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9(x_19, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_19);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_21);
x_35 = l_Lean_Syntax_getArg(x_19, x_9);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = lean_erase_macro_scopes(x_36);
x_38 = lean_unbox(x_13);
lean_dec(x_13);
x_39 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2(x_38, x_19, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_6);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
lean_dec(x_6);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getSepArgs(x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_12;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_isNone(x_1);
x_15 = l_Lean_Syntax_isNone(x_2);
x_16 = l_Lean_Syntax_isNone(x_3);
if (x_14 == 0)
{
if (x_15 == 0)
{
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 3, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 1;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 2, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 3, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
else
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 1;
x_29 = 0;
x_30 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 1, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 2, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
}
}
else
{
if (x_15 == 0)
{
if (x_16 == 0)
{
uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = 1;
x_34 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 3, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_13);
return x_35;
}
else
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 0;
x_37 = 1;
x_38 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 2, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 3, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
return x_39;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = 1;
x_42 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_6);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 1, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 2, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 3, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_13);
return x_43;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 2, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 3, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
}
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_getOptional_x3f(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_16 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_6, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_7);
x_18 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_6, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_11);
lean_dec(x_7);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4;
x_2 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected visibility modifier");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_getOptional_x3f(x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4;
x_20 = lean_name_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6;
x_22 = lean_name_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_6);
x_23 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8;
x_24 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11(x_17, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_17);
x_29 = 1;
x_30 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_30;
}
}
else
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_17);
x_31 = 2;
x_32 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected doc string");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(5u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(x_16, x_20, x_18, x_12, x_14, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_16);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = l_Lean_Syntax_getArg(x_25, x_11);
if (lean_obj_tag(x_26) == 2)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_string_utf8_byte_size(x_27);
x_29 = lean_nat_sub(x_28, x_13);
lean_dec(x_28);
x_30 = lean_string_utf8_extract(x_27, x_9, x_29);
lean_dec(x_29);
lean_dec(x_27);
lean_ctor_set(x_21, 0, x_30);
x_31 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(x_16, x_20, x_18, x_12, x_14, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_16);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_free_object(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13(x_25, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = l_Lean_Syntax_getArg(x_43, x_11);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_string_utf8_byte_size(x_45);
x_47 = lean_nat_sub(x_46, x_13);
lean_dec(x_46);
x_48 = lean_string_utf8_extract(x_45, x_9, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(x_16, x_20, x_18, x_12, x_14, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_16);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_44);
x_52 = l_Lean_indentD(x_51);
x_53 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13(x_43, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_43);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2;
x_15 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a non-private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Environment_contains(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
lean_inc(x_2);
x_11 = l_Lean_mkPrivateName(x_2, x_1);
lean_inc(x_2);
x_12 = l_Lean_Environment_contains(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lean_Environment_contains(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2(x_1, x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
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
}
}
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
case 1:
{
lean_object* x_19; 
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_protectedExt;
lean_inc(x_2);
x_26 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_25, x_24, x_2);
x_27 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_st_ref_get(x_8, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_mkPrivateName(x_39, x_2);
lean_inc(x_40);
x_41 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_40);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
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
lean_object* l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_docStringExt;
x_16 = l_Lean_MapDeclarationExtension_insert___rarg(x_15, x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_16);
x_17 = lean_st_ref_set(x_8, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_28 = l_Lean_docStringExt;
x_29 = l_Lean_MapDeclarationExtension_insert___rarg(x_28, x_24, x_1, x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
x_31 = lean_st_ref_set(x_8, x_30, x_12);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
lean_object* l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = 0;
x_11 = l_Lean_Syntax_getPos_x3f(x_1, x_10);
x_12 = l_Lean_Syntax_getTailPos_x3f(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_FileMap_toPosition(x_9, x_13);
lean_inc(x_14);
x_15 = l_Lean_FileMap_leanPosToLspPos(x_9, x_14);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_FileMap_toPosition(x_9, x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_FileMap_leanPosToLspPos(x_9, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l_Lean_FileMap_toPosition(x_9, x_26);
lean_dec(x_26);
lean_inc(x_27);
x_28 = l_Lean_FileMap_leanPosToLspPos(x_9, x_27);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_29);
lean_inc(x_27);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_FileMap_toPosition(x_9, x_33);
lean_dec(x_33);
lean_inc(x_34);
x_35 = l_Lean_FileMap_leanPosToLspPos(x_9, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
}
}
}
lean_object* l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_declRangeExt;
x_16 = l_Lean_MapDeclarationExtension_insert___rarg(x_15, x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_16);
x_17 = lean_st_ref_set(x_8, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_28 = l_Lean_declRangeExt;
x_29 = l_Lean_MapDeclarationExtension_insert___rarg(x_28, x_24, x_1, x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
x_31 = lean_st_ref_set(x_8, x_30, x_12);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_isNone(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getId(x_16);
lean_inc(x_17);
x_18 = l_Lean_Name_append(x_2, x_17);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_5);
x_20 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(x_19, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (x_14 == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_inc(x_21);
x_24 = l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(x_21, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_21);
x_26 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_21, x_16, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_5);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_17);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_inc(x_39);
x_42 = l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(x_39, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_39);
x_44 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_39, x_16, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_5);
lean_dec(x_16);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_3);
lean_ctor_set(x_48, 2, x_17);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_47);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = 0;
x_51 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_17);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' constructor in a 'private' structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Elab_Modifiers_isProtected(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1(x_1, x_2, x_3, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Elab_Modifiers_isPrivate(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1(x_1, x_2, x_3, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' constructor in a 'private' structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName;
x_12 = l_Lean_Name_append(x_3, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_16, x_18);
lean_dec(x_16);
x_20 = l_Lean_Syntax_isNone(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_19, x_21);
lean_dec(x_19);
x_23 = l_Lean_Syntax_getArg(x_22, x_21);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 3);
x_26 = l_Lean_replaceRef(x_22, x_25);
lean_dec(x_25);
lean_ctor_set(x_8, 3, x_26);
lean_inc(x_8);
lean_inc(x_4);
x_27 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_4);
x_30 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Modifiers_isPrivate(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(x_22, x_3, x_28, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_8);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(x_22, x_3, x_28, x_2, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_22);
x_38 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2;
x_39 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_27);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_8, 0);
x_53 = lean_ctor_get(x_8, 1);
x_54 = lean_ctor_get(x_8, 2);
x_55 = lean_ctor_get(x_8, 3);
x_56 = lean_ctor_get(x_8, 4);
x_57 = lean_ctor_get(x_8, 5);
x_58 = lean_ctor_get(x_8, 6);
x_59 = lean_ctor_get(x_8, 7);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_8);
x_60 = l_Lean_replaceRef(x_22, x_55);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_59);
lean_inc(x_61);
lean_inc(x_4);
x_62 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(x_23, x_4, x_5, x_6, x_7, x_61, x_9, x_10);
lean_dec(x_23);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_4);
x_65 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15(x_63, x_4, x_5, x_6, x_7, x_61, x_9, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Elab_Modifiers_isPrivate(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
x_69 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(x_22, x_3, x_63, x_2, x_68, x_4, x_5, x_6, x_7, x_61, x_9, x_66);
lean_dec(x_61);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(x_22, x_3, x_63, x_2, x_71, x_4, x_5, x_6, x_7, x_61, x_9, x_66);
lean_dec(x_61);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_63);
lean_dec(x_22);
x_73 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2;
x_74 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_73, x_4, x_5, x_6, x_7, x_61, x_9, x_66);
lean_dec(x_61);
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
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_4);
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_4);
x_83 = lean_ctor_get(x_62, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_85 = x_62;
} else {
 lean_dec_ref(x_62);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_19);
lean_inc(x_12);
x_87 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_12, x_14, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_14);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3;
x_91 = 0;
x_92 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_11);
lean_ctor_set(x_92, 3, x_12);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3;
x_95 = 0;
x_96 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_11);
lean_ctor_set(x_96, 3, x_12);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_16);
lean_inc(x_12);
x_98 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_12, x_14, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_14);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
x_101 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3;
x_102 = 0;
x_103 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_11);
lean_ctor_set(x_103, 3, x_12);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_98, 0, x_103);
return x_98;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3;
x_106 = 0;
x_107 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set(x_107, 2, x_11);
lean_ctor_set(x_107, 3, x_12);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addDocString___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private fields are not supported yet");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Elab_Modifiers_isPrivate(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in field declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__1(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in field declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in field declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in field declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__4(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_checkValidFieldModifier___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_checkValidFieldModifier(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_inc(x_2);
x_19 = l_Lean_Name_append(x_1, x_2);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_12);
x_21 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(x_20, x_19, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_inc(x_22);
x_25 = l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(x_22, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_2);
lean_ctor_set(x_28, 4, x_7);
lean_ctor_set(x_28, 5, x_8);
lean_ctor_set(x_28, 6, x_9);
lean_ctor_set_uint8(x_28, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 1, x_6);
x_29 = lean_array_push(x_10, x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_2);
lean_ctor_set(x_31, 4, x_7);
lean_ctor_set(x_31, 5, x_8);
lean_ctor_set(x_31, 6, x_9);
lean_ctor_set_uint8(x_31, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 1, x_6);
x_32 = lean_array_push(x_10, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field name '");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', identifiers starting with '_' are reserved to the system");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = x_9 == x_10;
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_array_uget(x_8, x_9);
x_21 = l_Lean_Syntax_getId(x_20);
x_22 = l_Lean_isInternalSubobjectFieldName(x_21);
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_25 = lean_ctor_get(x_16, 2);
x_26 = lean_ctor_get(x_16, 3);
x_27 = lean_ctor_get(x_16, 4);
x_28 = lean_ctor_get(x_16, 5);
x_29 = lean_ctor_get(x_16, 6);
x_30 = lean_ctor_get(x_16, 7);
x_31 = l_Lean_replaceRef(x_20, x_26);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
if (x_22 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_34 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1(x_1, x_21, x_3, x_20, x_2, x_4, x_5, x_6, x_7, x_11, x_33, x_12, x_13, x_14, x_15, x_32, x_17, x_18);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = x_9 + x_37;
x_9 = x_38;
x_11 = x_35;
x_18 = x_36;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_21);
x_45 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_48, x_12, x_13, x_14, x_15, x_32, x_17, x_18);
lean_dec(x_32);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_11);
lean_ctor_set(x_54, 1, x_18);
return x_54;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_234_(x_2, x_17);
if (x_16 == 0)
{
uint8_t x_61; 
x_61 = 1;
x_19 = x_61;
goto block_60;
}
else
{
uint8_t x_62; 
x_62 = 0;
x_19 = x_62;
goto block_60;
}
block_60:
{
lean_object* x_20; 
if (x_18 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_unsigned_to_nat(4u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
x_49 = l_Lean_Elab_expandDeclSig(x_48);
lean_dec(x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_49, 1, x_52);
x_20 = x_49;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_20 = x_56;
goto block_46;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_unsigned_to_nat(4u);
x_58 = l_Lean_Syntax_getArg(x_1, x_57);
x_59 = l_Lean_Elab_expandOptDeclSig(x_58);
lean_dec(x_58);
x_20 = x_59;
goto block_46;
}
block_46:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_18 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_29 = x_37;
goto block_36;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(5u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
x_40 = l_Lean_Syntax_isNone(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_Syntax_getArg(x_39, x_27);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_41, x_42);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_29 = x_44;
goto block_36;
}
else
{
lean_object* x_45; 
lean_dec(x_39);
x_45 = lean_box(0);
x_29 = x_45;
goto block_36;
}
}
block_36:
{
if (x_28 == 0)
{
lean_object* x_30; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_26, x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_35 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1(x_4, x_2, x_5, x_19, x_21, x_22, x_29, x_25, x_33, x_34, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_25);
return x_35;
}
}
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' field in a 'private' structure");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Elab_Modifiers_isProtected(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Elab_Modifiers_isPrivate(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2;
x_22 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' field in a 'private' structure");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_inc(x_10);
lean_inc(x_6);
x_15 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
x_18 = l_Lean_Elab_Command_checkValidFieldModifier(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Modifiers_isPrivate(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2(x_1, x_5, x_2, x_3, x_16, x_4, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_Elab_Modifiers_isPrivate(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2(x_1, x_5, x_2, x_3, x_16, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_2);
x_26 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2;
x_27 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_10);
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
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structExplicitBinder");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structImplicitBinder");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstBinder");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of structure field");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
x_13 = l_Lean_Syntax_getKind(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2;
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4;
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6;
x_19 = lean_name_eq(x_13, x_18);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8;
x_21 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 3;
x_27 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(x_4, x_1, x_2, x_3, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_27;
}
}
else
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_13);
x_28 = 1;
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(x_4, x_1, x_2, x_3, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_13);
x_30 = 0;
x_31 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(x_4, x_1, x_2, x_3, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_31;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structSimpleBinder");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_4 == x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_array_uget(x_3, x_4);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getKind(x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2;
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 2);
x_22 = lean_ctor_get(x_11, 3);
x_23 = lean_ctor_get(x_11, 4);
x_24 = lean_ctor_get(x_11, 5);
x_25 = lean_ctor_get(x_11, 6);
x_26 = lean_ctor_get(x_11, 7);
x_27 = l_Lean_replaceRef(x_15, x_22);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_25);
lean_ctor_set(x_28, 7, x_26);
if (x_18 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
lean_inc(x_7);
x_30 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(x_6, x_2, x_1, x_15, x_29, x_7, x_8, x_9, x_10, x_28, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 1;
x_34 = x_4 + x_33;
x_4 = x_34;
x_6 = x_31;
x_13 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_15, x_40);
x_42 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3;
x_43 = l_Lean_mkAtomFrom(x_15, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_15, x_44);
x_46 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
x_47 = lean_array_push(x_46, x_45);
x_48 = l_Lean_nullKind;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_15, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Syntax_getArg(x_15, x_52);
x_54 = lean_unsigned_to_nat(4u);
x_55 = l_Lean_Syntax_getArg(x_15, x_54);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5;
x_57 = l_Lean_mkAtomFrom(x_15, x_56);
lean_dec(x_15);
x_58 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6;
x_59 = lean_array_push(x_58, x_41);
x_60 = lean_array_push(x_59, x_43);
x_61 = lean_array_push(x_60, x_49);
x_62 = lean_array_push(x_61, x_51);
x_63 = lean_array_push(x_62, x_53);
x_64 = lean_array_push(x_63, x_55);
x_65 = lean_array_push(x_64, x_57);
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
lean_inc(x_7);
x_69 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(x_6, x_2, x_1, x_67, x_68, x_7, x_8, x_9, x_10, x_28, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 1;
x_73 = x_4 + x_72;
x_4 = x_73;
x_6 = x_70;
x_13 = x_71;
goto _start;
}
else
{
uint8_t x_75; 
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_7);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_13);
return x_79;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_4 == x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_array_uget(x_3, x_4);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getKind(x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2;
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 2);
x_22 = lean_ctor_get(x_11, 3);
x_23 = lean_ctor_get(x_11, 4);
x_24 = lean_ctor_get(x_11, 5);
x_25 = lean_ctor_get(x_11, 6);
x_26 = lean_ctor_get(x_11, 7);
x_27 = l_Lean_replaceRef(x_15, x_22);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_25);
lean_ctor_set(x_28, 7, x_26);
if (x_18 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
lean_inc(x_7);
x_30 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(x_6, x_2, x_1, x_15, x_29, x_7, x_8, x_9, x_10, x_28, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 1;
x_34 = x_4 + x_33;
x_4 = x_34;
x_6 = x_31;
x_13 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_15, x_40);
x_42 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3;
x_43 = l_Lean_mkAtomFrom(x_15, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_15, x_44);
x_46 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
x_47 = lean_array_push(x_46, x_45);
x_48 = l_Lean_nullKind;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_15, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Syntax_getArg(x_15, x_52);
x_54 = lean_unsigned_to_nat(4u);
x_55 = l_Lean_Syntax_getArg(x_15, x_54);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5;
x_57 = l_Lean_mkAtomFrom(x_15, x_56);
lean_dec(x_15);
x_58 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6;
x_59 = lean_array_push(x_58, x_41);
x_60 = lean_array_push(x_59, x_43);
x_61 = lean_array_push(x_60, x_49);
x_62 = lean_array_push(x_61, x_51);
x_63 = lean_array_push(x_62, x_53);
x_64 = lean_array_push(x_63, x_55);
x_65 = lean_array_push(x_64, x_57);
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
lean_inc(x_7);
x_69 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(x_6, x_2, x_1, x_67, x_68, x_7, x_8, x_9, x_10, x_28, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 1;
x_73 = x_4 + x_72;
x_4 = x_73;
x_6 = x_70;
x_13 = x_71;
goto _start;
}
else
{
uint8_t x_75; 
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_7);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_13);
return x_79;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_12, x_14);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_21 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_19, x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_24 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_28 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3(x_2, x_3, x_18, x_26, x_27, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
x_30 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__2;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_31 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__3;
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_34 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
else
{
size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; 
x_36 = 0;
x_37 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_38 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4(x_2, x_3, x_37, x_36, x_38, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_39;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
return x_21;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1(x_1, x_19, x_3, x_20, x_5, x_6, x_7, x_8, x_21, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_23;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__4(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_isStructure(x_15, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_11);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_10);
x_30 = l_Lean_isStructure(x_29, x_10);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_10);
x_32 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
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
else
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_28);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
x_42 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2;
x_43 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_43;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = x_5 + x_11;
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1;
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1(x_2, x_6, x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
x_17 = l_Lean_Name_append(x_1, x_2);
x_18 = lean_box(0);
x_19 = 1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*4 + 1, x_20);
x_22 = lean_array_push(x_3, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
x_25 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg(x_1, x_5, x_6, x_7, x_8, x_24, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkProjection(x_1, x_2, x_12, x_13, x_14, x_15, x_16);
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
lean_inc(x_18);
x_20 = l_Lean_Meta_inferType(x_18, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1___boxed), 16, 8);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, x_5);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_8);
x_24 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_2, x_21, x_18, x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' from '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_6, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_apply_8(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_fget(x_4, x_6);
x_19 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2(x_2, x_18, x_1, x_7, x_6, x_3, x_4, x_5, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_3);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg), 14, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg(x_1, x_2, x_3, x_4, x_6, x_14, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields___rarg), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg(x_2, x_13, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Name_append(x_16, x_2);
x_18 = lean_box(0);
x_19 = 2;
x_20 = 0;
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_8);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*4 + 1, x_20);
x_22 = lean_array_push(x_3, x_21);
x_23 = 1;
lean_inc(x_5);
x_24 = l_Lean_getStructureFieldsFlattened(x_4, x_5, x_23);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1___boxed), 11, 3);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg(x_16, x_8, x_5, x_24, x_25, x_26, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_27;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_st_ref_get(x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_4);
lean_inc(x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__2), 15, 7);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
if (x_20 == 0)
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_4);
x_22 = 0;
x_23 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_2, x_22, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_is_class(x_19, x_4);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_2, x_25, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = 3;
x_28 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_2, x_27, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_28;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("to");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_8(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget(x_12, x_2);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 3);
x_19 = l_Lean_replaceRef(x_16, x_18);
lean_dec(x_18);
lean_ctor_set(x_9, 3, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_20 = l_Lean_Elab_Term_elabType(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_5);
x_23 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure(x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_erase_macro_scopes(x_24);
x_27 = l_Lean_Name_getString_x21(x_26);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_name_mk_string(x_30, x_29);
x_32 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(x_3, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3(x_1, x_31, x_3, x_24, x_2, x_4, x_21, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_36 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_16, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_16);
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
}
else
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_23);
if (x_45 == 0)
{
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
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
lean_dec(x_9);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
x_55 = lean_ctor_get(x_9, 2);
x_56 = lean_ctor_get(x_9, 3);
x_57 = lean_ctor_get(x_9, 4);
x_58 = lean_ctor_get(x_9, 5);
x_59 = lean_ctor_get(x_9, 6);
x_60 = lean_ctor_get(x_9, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_61 = l_Lean_replaceRef(x_16, x_56);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_59);
lean_ctor_set(x_62, 7, x_60);
lean_inc(x_10);
lean_inc(x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_63 = l_Lean_Elab_Term_elabType(x_16, x_5, x_6, x_7, x_8, x_62, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_5);
x_66 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure(x_64, x_5, x_6, x_7, x_8, x_62, x_10, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_67);
x_69 = lean_erase_macro_scopes(x_67);
x_70 = l_Lean_Name_getString_x21(x_69);
lean_dec(x_69);
x_71 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = lean_name_mk_string(x_73, x_72);
x_75 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_containsFieldName(x_3, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_16);
x_76 = lean_box(0);
x_77 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3(x_1, x_74, x_3, x_67, x_2, x_4, x_64, x_76, x_5, x_6, x_7, x_8, x_62, x_10, x_68);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_78, 0, x_74);
x_79 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_16, x_82, x_5, x_6, x_7, x_8, x_62, x_10, x_68);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_16);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_ctor_get(x_66, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_90 = x_66;
} else {
 lean_dec_ref(x_66);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_62);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_ctor_get(x_63, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_63, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_94 = x_63;
} else {
 lean_dec_ref(x_63);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1() {
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = 0;
x_17 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_16, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_5);
lean_inc(x_3);
x_20 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Elab_Term_elabTerm(x_15, x_23, x_24, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_mkLambdaFVars(x_21, x_26, x_16, x_24, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_11, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_11);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_11, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_11);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_free_object(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
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
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = 0;
x_54 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_53, x_53, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_5);
lean_inc(x_3);
x_57 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
x_61 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Elab_Term_elabTerm(x_52, x_60, x_61, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_mkLambdaFVars(x_58, x_63, x_53, x_61, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_74 = x_65;
} else {
 lean_dec_ref(x_65);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = lean_ctor_get(x_62, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_78 = x_62;
} else {
 lean_dec_ref(x_62);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_ctor_get(x_57, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_57, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_82 = x_57;
} else {
 lean_dec_ref(x_57);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = lean_ctor_get(x_55, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_55, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_86 = x_55;
} else {
 lean_dec_ref(x_55);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_10);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_10, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l_Lean_Elab_Term_elabType(x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = 0;
x_94 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_95 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_93, x_93, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_5);
lean_inc(x_3);
x_97 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_1, 6);
lean_inc(x_98);
lean_dec(x_1);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = 1;
x_102 = l_Lean_Meta_mkForallFVars(x_99, x_91, x_93, x_101, x_5, x_6, x_7, x_8, x_100);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
lean_ctor_set(x_10, 0, x_104);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_10);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_102, 0, x_106);
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
lean_ctor_set(x_10, 0, x_107);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_free_object(x_10);
x_112 = !lean_is_exclusive(x_102);
if (x_112 == 0)
{
return x_102;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_102, 0);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_102);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_97, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_97, 1);
lean_inc(x_117);
lean_dec(x_97);
x_118 = !lean_is_exclusive(x_98);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_98, 0);
lean_inc(x_91);
lean_ctor_set(x_98, 0, x_91);
x_120 = lean_box(0);
x_121 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_122 = l_Lean_Elab_Term_elabTermEnsuringType(x_119, x_98, x_121, x_121, x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_125 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_93, x_93, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_5);
lean_inc(x_116);
x_127 = l_Lean_Meta_mkForallFVars(x_116, x_91, x_93, x_121, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Meta_mkLambdaFVars(x_116, x_123, x_93, x_121, x_5, x_6, x_7, x_8, x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
lean_ctor_set(x_10, 0, x_128);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_10);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_130, 0);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_130);
lean_ctor_set(x_10, 0, x_128);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_10);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_128);
lean_free_object(x_10);
x_140 = !lean_is_exclusive(x_130);
if (x_140 == 0)
{
return x_130;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_130, 0);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_130);
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
lean_dec(x_123);
lean_dec(x_116);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_144 = !lean_is_exclusive(x_127);
if (x_144 == 0)
{
return x_127;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_127, 0);
x_146 = lean_ctor_get(x_127, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_127);
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
lean_dec(x_123);
lean_dec(x_116);
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_148 = !lean_is_exclusive(x_125);
if (x_148 == 0)
{
return x_125;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_125, 0);
x_150 = lean_ctor_get(x_125, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_125);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_116);
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_122);
if (x_152 == 0)
{
return x_122;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_122, 0);
x_154 = lean_ctor_get(x_122, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_122);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_98, 0);
lean_inc(x_156);
lean_dec(x_98);
lean_inc(x_91);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_91);
x_158 = lean_box(0);
x_159 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_160 = l_Lean_Elab_Term_elabTermEnsuringType(x_156, x_157, x_159, x_159, x_158, x_3, x_4, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_163 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_93, x_93, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_inc(x_5);
lean_inc(x_116);
x_165 = l_Lean_Meta_mkForallFVars(x_116, x_91, x_93, x_159, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Meta_mkLambdaFVars(x_116, x_161, x_93, x_159, x_5, x_6, x_7, x_8, x_167);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_166);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_169);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_10);
lean_ctor_set(x_173, 1, x_172);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_171;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_166);
lean_free_object(x_10);
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_161);
lean_dec(x_116);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = lean_ctor_get(x_165, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_165, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_181 = x_165;
} else {
 lean_dec_ref(x_165);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_161);
lean_dec(x_116);
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_183 = lean_ctor_get(x_163, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_163, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_185 = x_163;
} else {
 lean_dec_ref(x_163);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_116);
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_160, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_160, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_189 = x_160;
} else {
 lean_dec_ref(x_160);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_97);
if (x_191 == 0)
{
return x_97;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_97, 0);
x_193 = lean_ctor_get(x_97, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_97);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_91);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_95);
if (x_195 == 0)
{
return x_95;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_95, 0);
x_197 = lean_ctor_get(x_95, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_95);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_90);
if (x_199 == 0)
{
return x_90;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_90, 0);
x_201 = lean_ctor_get(x_90, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_90);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_10, 0);
lean_inc(x_203);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_204 = l_Lean_Elab_Term_elabType(x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = 0;
x_208 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_209 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_207, x_207, x_208, x_3, x_4, x_5, x_6, x_7, x_8, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
lean_inc(x_5);
lean_inc(x_3);
x_211 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_1, 6);
lean_inc(x_212);
lean_dec(x_1);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
lean_dec(x_4);
lean_dec(x_3);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = 1;
x_216 = l_Lean_Meta_mkForallFVars(x_213, x_205, x_207, x_215, x_5, x_6, x_7, x_8, x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
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
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_217);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
if (lean_is_scalar(x_219)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_219;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_218);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_216, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_216, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_226 = x_216;
} else {
 lean_dec_ref(x_216);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_211, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_211, 1);
lean_inc(x_229);
lean_dec(x_211);
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_231 = x_212;
} else {
 lean_dec_ref(x_212);
 x_231 = lean_box(0);
}
lean_inc(x_205);
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_205);
x_233 = lean_box(0);
x_234 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_235 = l_Lean_Elab_Term_elabTermEnsuringType(x_230, x_232, x_234, x_234, x_233, x_3, x_4, x_5, x_6, x_7, x_8, x_229);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_238 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_207, x_207, x_208, x_3, x_4, x_5, x_6, x_7, x_8, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
lean_inc(x_5);
lean_inc(x_228);
x_240 = l_Lean_Meta_mkForallFVars(x_228, x_205, x_207, x_234, x_5, x_6, x_7, x_8, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Meta_mkLambdaFVars(x_228, x_236, x_207, x_234, x_5, x_6, x_7, x_8, x_242);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_241);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_244);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
if (lean_is_scalar(x_246)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_246;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_245);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_241);
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_243, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_253 = x_243;
} else {
 lean_dec_ref(x_243);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_255 = lean_ctor_get(x_240, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_240, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_257 = x_240;
} else {
 lean_dec_ref(x_240);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_259 = lean_ctor_get(x_238, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_238, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_261 = x_238;
} else {
 lean_dec_ref(x_238);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_228);
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_263 = lean_ctor_get(x_235, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_235, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_265 = x_235;
} else {
 lean_dec_ref(x_235);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_267 = lean_ctor_get(x_211, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_211, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_269 = x_211;
} else {
 lean_dec_ref(x_211);
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
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = lean_ctor_get(x_209, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_209, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_273 = x_209;
} else {
 lean_dec_ref(x_209);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_275 = lean_ctor_get(x_204, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_204, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_277 = x_204;
} else {
 lean_dec_ref(x_204);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Term_withAutoBoundImplicit___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_10, x_2);
return x_11;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__4___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = 0;
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*4 + 1, x_17);
x_21 = lean_array_push(x_4, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
x_24 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(x_6, x_23, x_21, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_24;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_18 = 0;
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_8);
lean_ctor_set(x_19, 3, x_3);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4 + 1, x_17);
x_20 = lean_array_push(x_4, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
x_23 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(x_6, x_22, x_20, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_23;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_1);
x_19 = l_Lean_Meta_inferType(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_box(0);
x_24 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_25 = l_Lean_Elab_Term_elabTermEnsuringType(x_10, x_22, x_24, x_24, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_1);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_29, sizeof(void*)*4 + 1, x_5);
x_30 = lean_array_push(x_6, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_7, x_31);
x_33 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(x_8, x_32, x_30, x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field, type expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has been declared in parent structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4;
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6;
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("basicFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6;
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("omit field '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' type to set default value");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.Structure.0.Lean.Elab.Command.withFields");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21;
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22;
x_3 = lean_unsigned_to_nat(327u);
x_4 = lean_unsigned_to_nat(37u);
x_5 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_8(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f(x_3, x_17);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_20);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_21);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_22; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_22 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_30);
x_31 = l_Lean_Meta_inferType(x_30, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_35, 0, x_15);
lean_closure_set(x_35, 1, x_30);
lean_closure_set(x_35, 2, x_17);
lean_closure_set(x_35, 3, x_3);
lean_closure_set(x_35, 4, x_2);
lean_closure_set(x_35, 5, x_1);
lean_closure_set(x_35, 6, x_4);
x_36 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_17, x_34, x_32, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2___boxed), 15, 7);
lean_closure_set(x_45, 0, x_15);
lean_closure_set(x_45, 1, x_17);
lean_closure_set(x_45, 2, x_42);
lean_closure_set(x_45, 3, x_3);
lean_closure_set(x_45, 4, x_2);
lean_closure_set(x_45, 5, x_1);
lean_closure_set(x_45, 6, x_4);
x_46 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_17, x_44, x_43, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
switch (x_52) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_17);
x_54 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg(x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_58;
}
case 1:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_15, 6);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_17);
x_61 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg(x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_15, 5);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_17);
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_51, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_51, sizeof(void*)*4 + 1);
lean_dec(x_51);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
lean_dec(x_59);
x_72 = lean_ctor_get(x_15, 4);
lean_inc(x_72);
lean_dec(x_15);
x_73 = l_Lean_Syntax_getArgs(x_72);
lean_dec(x_72);
x_74 = lean_array_get_size(x_73);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
x_77 = lean_box(0);
x_78 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(x_69, x_67, x_68, x_52, x_70, x_3, x_2, x_1, x_4, x_71, x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_79 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7;
lean_inc(x_80);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_89 = l_Array_append___rarg(x_88, x_73);
lean_dec(x_73);
x_90 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13;
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14;
x_95 = lean_array_push(x_94, x_91);
x_96 = lean_array_push(x_95, x_93);
x_97 = lean_array_push(x_96, x_71);
x_98 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15;
x_101 = lean_array_push(x_100, x_87);
x_102 = lean_array_push(x_101, x_99);
x_103 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_box(0);
x_106 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(x_69, x_67, x_68, x_52, x_70, x_3, x_2, x_1, x_4, x_104, x_105, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_2);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_66, 0);
lean_inc(x_107);
lean_dec(x_66);
x_108 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_108, 0, x_17);
x_109 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg(x_107, x_112, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_107);
return x_113;
}
}
}
default: 
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20;
x_115 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24;
x_116 = lean_panic_fn(x_114, x_115);
x_117 = lean_apply_7(x_116, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_9, 0);
x_119 = lean_ctor_get(x_9, 1);
x_120 = lean_ctor_get(x_9, 2);
x_121 = lean_ctor_get(x_9, 3);
x_122 = lean_ctor_get(x_9, 4);
x_123 = lean_ctor_get(x_9, 5);
x_124 = lean_ctor_get(x_9, 6);
x_125 = lean_ctor_get(x_9, 7);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_9);
x_126 = l_Lean_replaceRef(x_16, x_121);
lean_dec(x_121);
lean_dec(x_16);
x_127 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_126);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 5, x_123);
lean_ctor_set(x_127, 6, x_124);
lean_ctor_set(x_127, 7, x_125);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_128; 
lean_inc(x_10);
lean_inc(x_127);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_128 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue(x_15, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2;
x_134 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg(x_133, x_5, x_6, x_7, x_8, x_127, x_10, x_132);
lean_dec(x_10);
lean_dec(x_127);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_dec(x_128);
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
lean_dec(x_131);
lean_inc(x_10);
lean_inc(x_127);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_136);
x_137 = l_Lean_Meta_inferType(x_136, x_7, x_8, x_127, x_10, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_141 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_141, 0, x_15);
lean_closure_set(x_141, 1, x_136);
lean_closure_set(x_141, 2, x_17);
lean_closure_set(x_141, 3, x_3);
lean_closure_set(x_141, 4, x_2);
lean_closure_set(x_141, 5, x_1);
lean_closure_set(x_141, 6, x_4);
x_142 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_17, x_140, x_138, x_141, x_5, x_6, x_7, x_8, x_127, x_10, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_136);
lean_dec(x_127);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_145 = x_137;
} else {
 lean_dec_ref(x_137);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_dec(x_128);
x_148 = lean_ctor_get(x_129, 1);
lean_inc(x_148);
lean_dec(x_129);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
lean_dec(x_130);
x_150 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_151 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2___boxed), 15, 7);
lean_closure_set(x_151, 0, x_15);
lean_closure_set(x_151, 1, x_17);
lean_closure_set(x_151, 2, x_148);
lean_closure_set(x_151, 3, x_3);
lean_closure_set(x_151, 4, x_2);
lean_closure_set(x_151, 5, x_1);
lean_closure_set(x_151, 6, x_4);
x_152 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_17, x_150, x_149, x_151, x_5, x_6, x_7, x_8, x_127, x_10, x_147);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_127);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_128, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_128, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_155 = x_128;
} else {
 lean_dec_ref(x_128);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_18, 0);
lean_inc(x_157);
lean_dec(x_18);
x_158 = lean_ctor_get_uint8(x_157, sizeof(void*)*4);
switch (x_158) {
case 0:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_157);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_159, 0, x_17);
x_160 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_161 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_163 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg(x_163, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
lean_dec(x_10);
lean_dec(x_127);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_164;
}
case 1:
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_15, 6);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_157);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_166, 0, x_17);
x_167 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2;
x_168 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4;
x_170 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg(x_170, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
lean_dec(x_10);
lean_dec(x_127);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_171;
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_15, 5);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_17);
x_173 = lean_ctor_get(x_157, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_157, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_157, 2);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_157, sizeof(void*)*4 + 1);
lean_dec(x_157);
x_177 = lean_ctor_get(x_165, 0);
lean_inc(x_177);
lean_dec(x_165);
x_178 = lean_ctor_get(x_15, 4);
lean_inc(x_178);
lean_dec(x_15);
x_179 = l_Lean_Syntax_getArgs(x_178);
lean_dec(x_178);
x_180 = lean_array_get_size(x_179);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_nat_dec_lt(x_181, x_180);
lean_dec(x_180);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_179);
x_183 = lean_box(0);
x_184 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(x_175, x_173, x_174, x_158, x_176, x_3, x_2, x_1, x_4, x_177, x_183, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
lean_dec(x_2);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_185 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_127, x_10, x_11);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_127, x_10, x_187);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_189);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7;
lean_inc(x_186);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_195 = l_Array_append___rarg(x_194, x_179);
lean_dec(x_179);
x_196 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12;
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13;
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_186);
lean_ctor_set(x_199, 1, x_198);
x_200 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14;
x_201 = lean_array_push(x_200, x_197);
x_202 = lean_array_push(x_201, x_199);
x_203 = lean_array_push(x_202, x_177);
x_204 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10;
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15;
x_207 = lean_array_push(x_206, x_193);
x_208 = lean_array_push(x_207, x_205);
x_209 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8;
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_box(0);
x_212 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(x_175, x_173, x_174, x_158, x_176, x_3, x_2, x_1, x_4, x_210, x_211, x_5, x_6, x_7, x_8, x_127, x_10, x_191);
lean_dec(x_2);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_165);
lean_dec(x_157);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_172, 0);
lean_inc(x_213);
lean_dec(x_172);
x_214 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_214, 0, x_17);
x_215 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19;
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg(x_213, x_218, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_213);
return x_219;
}
}
}
default: 
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_157);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20;
x_221 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24;
x_222 = lean_panic_fn(x_220, x_221);
x_223 = lean_apply_7(x_222, x_5, x_6, x_7, x_8, x_127, x_10, x_11);
return x_223;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___lambda__3(x_1, x_2, x_3, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_11);
lean_dec(x_7);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2;
x_19 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 == x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Elab_Term_collectUsedFVars(x_15, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = lean_box(0);
x_2 = x_21;
x_4 = x_22;
x_10 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Lean_Elab_Term_collectUsedFVars(x_25, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = x_2 + x_29;
x_2 = x_30;
x_4 = x_27;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
x_12 = x_8;
goto block_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_9, x_9);
if (x_25 == 0)
{
lean_dec(x_9);
x_12 = x_8;
goto block_24;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_28 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_1, x_26, x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_12 = x_30;
goto block_24;
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
block_24:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1(x_2, x_20, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_12);
return x_23;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUsed(x_2, x_3, x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_9, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_removeUnused(x_1, x_22, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_apply_1(x_4, x_18);
x_20 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_16, x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_levelMVarToParam_x27(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_2 == x_3;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_2 + x_18;
x_2 = x_19;
x_4 = x_16;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1(x_1, x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*4 + 1);
x_24 = lean_ctor_get(x_18, 3);
lean_inc(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_25 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVar(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = x_2 + x_27;
x_29 = x_18;
x_30 = lean_array_uset(x_17, x_2, x_29);
x_2 = x_28;
x_3 = x_30;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_18, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_18, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_18, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = l_Lean_Elab_Term_levelMVarToParam_x27(x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_ctor_set(x_24, 0, x_41);
x_43 = 1;
x_44 = x_2 + x_43;
x_45 = x_18;
x_46 = lean_array_uset(x_17, x_2, x_45);
x_2 = x_44;
x_3 = x_46;
x_11 = x_42;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
lean_dec(x_24);
x_49 = l_Lean_Elab_Term_levelMVarToParam_x27(x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_18, 3, x_52);
x_53 = 1;
x_54 = x_2 + x_53;
x_55 = x_18;
x_56 = lean_array_uset(x_17, x_2, x_55);
x_2 = x_54;
x_3 = x_56;
x_11 = x_51;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_dec(x_25);
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_60 = x_24;
} else {
 lean_dec_ref(x_24);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Elab_Term_levelMVarToParam_x27(x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_65, 0, x_19);
lean_ctor_set(x_65, 1, x_20);
lean_ctor_set(x_65, 2, x_21);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_22);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 1, x_23);
x_66 = 1;
x_67 = x_2 + x_66;
x_68 = x_65;
x_69 = lean_array_uset(x_17, x_2, x_68);
x_2 = x_67;
x_3 = x_69;
x_11 = x_63;
goto _start;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
return x_25;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_25, 0);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_25);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamFVars(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = x_3;
x_19 = lean_box_usize(x_17);
x_20 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1;
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed), 11, 3);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_18);
x_22 = x_21;
x_23 = lean_apply_8(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
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
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_15);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux(x_1, x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_9, x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_15, x_21);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_4 == x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_3, x_4);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_inferType(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_getLevel(x_18, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_21, x_9, x_10, x_11, x_12, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_2);
x_26 = l_Lean_Elab_Command_accLevelAtCtor(x_24, x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = x_4 + x_29;
x_4 = x_30;
x_6 = x_27;
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_19, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of structure, provide universe explicitly");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux(x_11, x_13);
x_15 = l_Lean_Level_getLevelOffset(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectUniversesFromFields(x_15, x_14, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_mkResultUniverse(x_18, x_14);
lean_dec(x_14);
x_21 = l_Lean_Meta_assignLevelMVar(x_16, x_20, x_5, x_6, x_7, x_8, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_instantiateMVars(x_2, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_28 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2;
x_29 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_instantiateMVars(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_CollectLevelParams_main(x_15, x_1);
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
x_19 = l_Lean_CollectLevelParams_main(x_17, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar(x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_2 + x_17;
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1(x_1, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVar(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_2 + x_18;
x_2 = x_19;
x_4 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1;
x_2 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1;
x_13 = l_Lean_CollectLevelParams_main(x_1, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars(x_2, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInFVars(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_array_get_size(x_4);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_free_object(x_17);
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1(x_4, x_27, x_28, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_array_get_size(x_4);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = lean_ctor_get(x_41, 2);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_43, x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_49 = lean_ctor_get(x_41, 2);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_53 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1(x_4, x_51, x_52, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
lean_dec(x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
else
{
uint8_t x_63; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
return x_17;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_14);
if (x_67 == 0)
{
return x_14;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_14, 0);
x_69 = lean_ctor_get(x_14, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_14);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields_match__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_15 = l_Lean_Elab_Command_instInhabitedStructFieldInfo;
x_16 = lean_array_get(x_15, x_1, x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_instantiateMVars(x_3, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
x_25 = lean_array_push(x_24, x_17);
x_26 = lean_expr_abstract(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
lean_dec(x_16);
switch (x_27) {
case 0:
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_LocalDecl_userName(x_19);
x_29 = l_Lean_LocalDecl_binderInfo(x_19);
x_30 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_31 = l_Lean_mkForall(x_28, x_29, x_30, x_26);
x_2 = x_14;
x_3 = x_31;
x_10 = x_23;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_LocalDecl_value(x_19);
lean_dec(x_19);
x_34 = lean_expr_instantiate1(x_26, x_33);
lean_dec(x_33);
lean_dec(x_26);
x_2 = x_14;
x_3 = x_34;
x_10 = x_23;
goto _start;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = l_Lean_LocalDecl_userName(x_19);
x_37 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1;
x_38 = lean_name_append_before(x_36, x_37);
x_39 = l_Lean_LocalDecl_binderInfo(x_19);
x_40 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_41 = l_Lean_mkForall(x_38, x_39, x_40, x_26);
x_2 = x_14;
x_3 = x_41;
x_10 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
x_14 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_2);
x_15 = l_Lean_mkConst(x_13, x_14);
x_16 = l_Lean_mkAppN(x_15, x_3);
x_17 = lean_array_get_size(x_4);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 3);
x_20 = l_Lean_replaceRef(x_12, x_19);
lean_dec(x_19);
lean_dec(x_12);
lean_ctor_set(x_9, 3, x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields(x_4, x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = 1;
lean_inc(x_7);
lean_inc(x_3);
x_26 = l_Lean_Meta_mkForallFVars(x_3, x_22, x_24, x_25, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_instantiateMVars(x_27, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_array_get_size(x_3);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 9);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_inferImplicit(x_31, x_32, x_25);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 3);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lean_Expr_inferImplicit(x_31, x_32, x_24);
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_43 = lean_array_get_size(x_3);
lean_dec(x_3);
x_44 = lean_ctor_get(x_1, 9);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Expr_inferImplicit(x_41, x_43, x_25);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Lean_Expr_inferImplicit(x_41, x_43, x_24);
lean_dec(x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
return x_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
return x_21;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_21, 0);
x_64 = lean_ctor_get(x_21, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_21);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
x_68 = lean_ctor_get(x_9, 2);
x_69 = lean_ctor_get(x_9, 3);
x_70 = lean_ctor_get(x_9, 4);
x_71 = lean_ctor_get(x_9, 5);
x_72 = lean_ctor_get(x_9, 6);
x_73 = lean_ctor_get(x_9, 7);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_74 = l_Lean_replaceRef(x_12, x_69);
lean_dec(x_69);
lean_dec(x_12);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_67);
lean_ctor_set(x_75, 2, x_68);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_70);
lean_ctor_set(x_75, 5, x_71);
lean_ctor_set(x_75, 6, x_72);
lean_ctor_set(x_75, 7, x_73);
lean_inc(x_10);
lean_inc(x_75);
lean_inc(x_8);
lean_inc(x_7);
x_76 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields(x_4, x_17, x_16, x_5, x_6, x_7, x_8, x_75, x_10, x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = 0;
x_80 = 1;
lean_inc(x_7);
lean_inc(x_3);
x_81 = l_Lean_Meta_mkForallFVars(x_3, x_77, x_79, x_80, x_7, x_8, x_75, x_10, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_instantiateMVars(x_82, x_7, x_8, x_75, x_10, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
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
x_88 = lean_array_get_size(x_3);
lean_dec(x_3);
x_89 = lean_ctor_get(x_1, 9);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_89, 3);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Expr_inferImplicit(x_85, x_88, x_80);
lean_dec(x_88);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_87)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_87;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 3);
lean_inc(x_95);
lean_dec(x_89);
x_96 = l_Lean_Expr_inferImplicit(x_85, x_88, x_79);
lean_dec(x_88);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_87)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_87;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_86);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_101 = x_84;
} else {
 lean_dec_ref(x_84);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_103 = lean_ctor_get(x_81, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_76, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_109 = x_76;
} else {
 lean_dec_ref(x_76);
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
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_mk_projections(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_projections(x_14, x_1, x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_8);
lean_dec(x_4);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
if (x_3 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Environment_contains(x_12, x_13);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4;
lean_inc(x_12);
x_16 = l_Lean_Environment_contains(x_12, x_15);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6;
x_18 = l_Lean_Environment_contains(x_12, x_17);
lean_inc(x_6);
lean_inc(x_2);
x_19 = l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_19) == 0)
{
if (x_14 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1(x_14, x_16, x_18, x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_2);
x_24 = l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1(x_14, x_16, x_18, x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___lambda__1(x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_set_reducibility_status(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_8, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = lean_set_reducibility_status(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_8, x_28, x_12);
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
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_mkId(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkAuxDefinition(x_2, x_3, x_13, x_15, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1(x_2, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
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
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid default value for field, it contains metavariables");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_instantiateMVars(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_hasExprMVar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1(x_19, x_15, x_16, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = x_2 + x_26;
x_2 = x_27;
x_4 = x_24;
x_11 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_15);
x_33 = l_Lean_indentExpr(x_19);
x_34 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_11);
return x_47;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = l_Lean_Meta_getLocalInstances(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_2);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1;
x_17 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_1, x_11, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_13, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_2);
x_19 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1;
x_20 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_1, x_11, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_20;
}
else
{
size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1;
x_24 = lean_box_usize(x_21);
x_25 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___boxed), 11, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_22);
x_26 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_1, x_11, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_26;
}
}
}
}
lean_object* l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_setReducibilityStatus___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 1);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__1(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4 + 1);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_unsigned_to_nat(1000u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_addInstance(x_11, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_12;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option.get!");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_inferType(x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2;
x_24 = l_Lean_Name_append(x_22, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_17, 3);
lean_inc(x_25);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_26 = l_Lean_instInhabitedExpr;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = 1;
x_32 = x_2 + x_31;
x_33 = x_30;
x_34 = lean_array_uset(x_16, x_2, x_33);
x_2 = x_32;
x_3 = x_34;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = 1;
x_40 = x_2 + x_39;
x_41 = x_38;
x_42 = lean_array_uset(x_16, x_2, x_41);
x_2 = x_40;
x_3 = x_42;
x_10 = x_21;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Lean_LocalContext_setBinderInfo(x_4, x_11, x_12);
x_2 = x_9;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = l_Lean_LocalContext_setBinderInfo(x_4, x_7, x_8);
x_10 = 1;
x_11 = x_2 + x_10;
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = 1;
x_9 = x_2 + x_8;
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_array_push(x_4, x_6);
x_2 = x_9;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_StructFieldInfo_isSubobject(x_13);
if (x_18 == 0)
{
size_t x_19; size_t x_20; 
lean_dec(x_16);
lean_dec(x_13);
x_19 = 1;
x_20 = x_2 + x_19;
x_2 = x_20;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_22; uint8_t x_23; 
x_22 = l_Lean_LocalDecl_binderInfo(x_16);
lean_dec(x_16);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_22);
if (x_23 == 0)
{
size_t x_24; size_t x_25; 
lean_dec(x_13);
x_24 = 1;
x_25 = x_2 + x_24;
x_2 = x_25;
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_array_push(x_4, x_13);
x_28 = 1;
x_29 = x_2 + x_28;
x_2 = x_29;
x_4 = x_27;
x_11 = x_17;
goto _start;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_6);
x_2 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__20(x_10, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_12;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', it is equal to structure constructor name");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_3 == x_4;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 9);
x_17 = lean_ctor_get(x_16, 3);
x_18 = lean_name_eq(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1(x_14, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_5 = x_21;
x_12 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 3);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_26, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_26);
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
lean_dec(x_10);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 3);
lean_inc(x_20);
x_21 = l_Lean_Elab_sortDeclLevelParams(x_19, x_20, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 3);
x_27 = l_Lean_replaceRef(x_6, x_26);
lean_dec(x_26);
lean_ctor_set(x_13, 3, x_27);
x_28 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_ctor_get(x_13, 2);
x_32 = lean_ctor_get(x_13, 3);
x_33 = lean_ctor_get(x_13, 4);
x_34 = lean_ctor_get(x_13, 5);
x_35 = lean_ctor_get(x_13, 6);
x_36 = lean_ctor_get(x_13, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_37 = l_Lean_replaceRef(x_6, x_32);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
x_39 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_24, x_9, x_10, x_11, x_12, x_38, x_14, x_18);
lean_dec(x_14);
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
lean_dec(x_21);
x_41 = l_Array_append___rarg(x_2, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_5);
x_42 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkCtor(x_5, x_40, x_41, x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = 0;
x_46 = 1;
lean_inc(x_11);
lean_inc(x_41);
x_47 = l_Lean_Meta_mkForallFVars(x_41, x_1, x_45, x_46, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Lean_Meta_instantiateMVars(x_48, x_11, x_12, x_13, x_14, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_5, 4);
lean_inc(x_53);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_53);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_array_get_size(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_54);
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*2 + 3);
lean_inc(x_57);
x_61 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_60);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_61);
x_62 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_61, x_9, x_10, x_11, x_12, x_13, x_14, x_52);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_13);
lean_inc(x_9);
x_64 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_61, x_9, x_10, x_11, x_12, x_13, x_14, x_63);
lean_dec(x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_array_get_size(x_4);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_68 == 0)
{
lean_inc(x_7);
x_70 = x_7;
goto block_157;
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_66, x_66);
if (x_158 == 0)
{
lean_inc(x_7);
x_70 = x_7;
goto block_157;
}
else
{
size_t x_159; size_t x_160; lean_object* x_161; 
x_159 = 0;
x_160 = lean_usize_of_nat(x_66);
lean_inc(x_7);
x_161 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9(x_4, x_159, x_160, x_7);
x_70 = x_161;
goto block_157;
}
}
block_157:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_array_to_list(lean_box(0), x_70);
x_72 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__1(x_71);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_53);
x_73 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addProjections(x_53, x_72, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
lean_inc(x_13);
lean_inc(x_9);
x_75 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions(x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
if (x_68 == 0)
{
lean_inc(x_7);
x_77 = x_7;
x_78 = x_76;
goto block_138;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_66, x_66);
if (x_139 == 0)
{
lean_inc(x_7);
x_77 = x_7;
x_78 = x_76;
goto block_138;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_66);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_142 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8(x_4, x_140, x_141, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_77 = x_143;
x_78 = x_144;
goto block_138;
}
else
{
uint8_t x_145; 
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_145 = !lean_is_exclusive(x_142);
if (x_145 == 0)
{
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
block_138:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_79 = lean_array_to_list(lean_box(0), x_77);
x_80 = l_List_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__2(x_79);
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_dec(x_59);
x_82 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
x_83 = l_Lean_Elab_Term_applyAttributesAt(x_53, x_81, x_82, x_9, x_10, x_11, x_12, x_13, x_14, x_78);
lean_dec(x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_85 = l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3(x_80, x_9, x_10, x_11, x_12, x_13, x_14, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_11, 1);
lean_inc(x_87);
x_88 = 0;
if (x_68 == 0)
{
x_89 = x_7;
goto block_126;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_66, x_66);
if (x_127 == 0)
{
x_89 = x_7;
goto block_126;
}
else
{
size_t x_128; lean_object* x_129; 
x_128 = lean_usize_of_nat(x_66);
x_129 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7(x_4, x_88, x_128, x_7);
x_89 = x_129;
goto block_126;
}
}
block_126:
{
lean_object* x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_array_get_size(x_89);
x_91 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_92 = x_89;
x_93 = lean_box_usize(x_91);
x_94 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1;
x_95 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___boxed), 10, 3);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_94);
lean_closure_set(x_95, 2, x_92);
x_96 = x_95;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_97 = lean_apply_7(x_96, x_9, x_10, x_11, x_12, x_13, x_14, x_86);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_nat_dec_lt(x_67, x_57);
if (x_100 == 0)
{
lean_dec(x_57);
lean_dec(x_41);
if (x_68 == 0)
{
lean_object* x_101; 
lean_dec(x_66);
x_101 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_87, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_le(x_66, x_66);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_66);
x_103 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_87, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_103;
}
else
{
size_t x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_105 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(x_4, x_88, x_104, x_87);
x_106 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_105, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_106;
}
}
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_57, x_57);
if (x_107 == 0)
{
lean_dec(x_57);
lean_dec(x_41);
if (x_68 == 0)
{
lean_object* x_108; 
lean_dec(x_66);
x_108 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_87, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_108;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_66, x_66);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_66);
x_110 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_87, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_110;
}
else
{
size_t x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_112 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(x_4, x_88, x_111, x_87);
x_113 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_112, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_113;
}
}
}
else
{
size_t x_114; lean_object* x_115; 
x_114 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_115 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6(x_41, x_88, x_114, x_87);
lean_dec(x_41);
if (x_68 == 0)
{
lean_object* x_116; 
lean_dec(x_66);
x_116 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_115, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_116;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_66, x_66);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_66);
x_118 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_115, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_118;
}
else
{
size_t x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_120 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(x_4, x_88, x_119, x_115);
x_121 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults(x_120, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
return x_121;
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_87);
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_122 = !lean_is_exclusive(x_97);
if (x_122 == 0)
{
return x_97;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_97, 0);
x_124 = lean_ctor_get(x_97, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_97);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_130 = !lean_is_exclusive(x_85);
if (x_130 == 0)
{
return x_85;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_85, 0);
x_132 = lean_ctor_get(x_85, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_85);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_80);
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_134 = !lean_is_exclusive(x_83);
if (x_134 == 0)
{
return x_83;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_83, 0);
x_136 = lean_ctor_get(x_83, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_83);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_149 = !lean_is_exclusive(x_75);
if (x_149 == 0)
{
return x_75;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_75, 0);
x_151 = lean_ctor_get(x_75, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_75);
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
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_153 = !lean_is_exclusive(x_73);
if (x_153 == 0)
{
return x_73;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_73, 0);
x_155 = lean_ctor_get(x_73, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_73);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_162 = !lean_is_exclusive(x_64);
if (x_162 == 0)
{
return x_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_64, 0);
x_164 = lean_ctor_get(x_64, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_64);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_166 = !lean_is_exclusive(x_62);
if (x_166 == 0)
{
return x_62;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_62, 0);
x_168 = lean_ctor_get(x_62, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_62);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_170 = !lean_is_exclusive(x_50);
if (x_170 == 0)
{
return x_50;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_50, 0);
x_172 = lean_ctor_get(x_50, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_50);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_47);
if (x_174 == 0)
{
return x_47;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_47, 0);
x_176 = lean_ctor_get(x_47, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_47);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_42);
if (x_178 == 0)
{
return x_42;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_42, 0);
x_180 = lean_ctor_get(x_42, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_42);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_16);
if (x_182 == 0)
{
return x_16;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_16, 0);
x_184 = lean_ctor_get(x_16, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_16);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2;
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParam(x_8, x_1, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_13, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_13, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_13, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_13, 7);
lean_inc(x_55);
x_56 = l_Lean_replaceRef(x_4, x_51);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_53);
lean_ctor_set(x_57, 6, x_54);
lean_ctor_set(x_57, 7, x_55);
if (x_6 == 0)
{
lean_object* x_58; 
lean_inc(x_14);
lean_inc(x_57);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
x_58 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(x_7, x_9, x_10, x_11, x_12, x_57, x_14, x_18);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_9);
x_61 = l_Lean_Elab_Command_checkResultingUniverse(x_59, x_9, x_10, x_11, x_12, x_57, x_14, x_60);
lean_dec(x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_19 = x_7;
x_20 = x_62;
goto block_47;
}
else
{
uint8_t x_63; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_61);
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
lean_dec(x_57);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
return x_58;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_58, 0);
x_69 = lean_ctor_get(x_58, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_58);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_71 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse(x_17, x_7, x_9, x_10, x_11, x_12, x_57, x_14, x_18);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_19 = x_72;
x_20 = x_73;
goto block_47;
}
else
{
uint8_t x_74; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
block_47:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_21 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4;
x_36 = lean_st_ref_get(x_14, x_20);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = 0;
x_22 = x_41;
x_23 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_22 = x_46;
x_23 = x_45;
goto block_35;
}
block_35:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1(x_19, x_8, x_1, x_17, x_3, x_4, x_5, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_19);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_19);
x_27 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_21, x_30, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1(x_19, x_8, x_1, x_17, x_3, x_4, x_5, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
lean_dec(x_32);
lean_dec(x_17);
return x_34;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_16);
if (x_78 == 0)
{
return x_16;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_16, 0);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_16);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_13, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
x_20 = l_Lean_Elab_Command_shouldInferResultUniverse(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 6);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___boxed), 15, 7);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_21);
lean_closure_set(x_25, 6, x_1);
x_26 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withUsed___rarg(x_23, x_24, x_5, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_5);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
else
{
uint8_t x_27; 
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
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
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
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__3), 12, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg(x_5, x_15, x_6, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
lean_inc(x_12);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__4), 13, 5);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_3);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 3);
x_17 = l_Lean_replaceRef(x_12, x_16);
lean_dec(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 3, x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg(x_1, x_18, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_9, 5);
x_26 = lean_ctor_get(x_9, 6);
x_27 = lean_ctor_get(x_9, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_28 = l_Lean_replaceRef(x_12, x_23);
lean_dec(x_23);
lean_dec(x_12);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg(x_1, x_30, x_13, x_14, x_5, x_6, x_7, x_8, x_29, x_10, x_11);
return x_31;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected Type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_9 = lean_ctor_get(x_1, 10);
lean_inc(x_9);
x_29 = lean_array_get_size(x_9);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
x_10 = x_8;
goto block_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
lean_dec(x_29);
x_10 = x_8;
goto block_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_35 = lean_box(0);
lean_inc(x_6);
lean_inc(x_2);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10(x_1, x_9, x_33, x_34, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_10 = x_37;
goto block_28;
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_28:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 8);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_elabType(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_validStructType(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2;
x_17 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_11, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_11);
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
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5(x_1, x_13, x_9, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__8(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabStructure_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabStructure_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("class");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_12, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Elab_instInhabitedAttribute;
x_15 = lean_array_get(x_14, x_6, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4;
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_19, x_3, x_4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_9, x_3, x_4, x_5);
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
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_8, x_2, x_3, x_4);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 < x_2;
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
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_14, x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_15, x_24);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_25);
x_26 = l_Lean_Syntax_getId(x_10);
x_27 = lean_box(0);
lean_inc(x_5);
lean_inc(x_10);
x_28 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_10, x_26, x_27, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_23);
x_32 = lean_array_push(x_13, x_31);
lean_ctor_set(x_4, 1, x_32);
x_33 = 1;
x_34 = x_3 + x_33;
x_3 = x_34;
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
x_40 = lean_array_fget(x_14, x_15);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_15, x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_16);
x_44 = l_Lean_Syntax_getId(x_10);
x_45 = lean_box(0);
lean_inc(x_5);
lean_inc(x_10);
x_46 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_10, x_44, x_45, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_40);
x_50 = lean_array_push(x_13, x_49);
lean_ctor_set(x_4, 1, x_50);
lean_ctor_set(x_4, 0, x_43);
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
x_7 = x_48;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
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
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_4);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_nat_dec_lt(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_5);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
x_67 = lean_array_fget(x_60, x_61);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_61, x_68);
lean_dec(x_61);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_62);
x_71 = l_Lean_Syntax_getId(x_10);
x_72 = lean_box(0);
lean_inc(x_5);
lean_inc(x_10);
x_73 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_10, x_71, x_72, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_10);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_67);
x_77 = lean_array_push(x_59, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_77);
x_79 = 1;
x_80 = x_3 + x_79;
x_3 = x_80;
x_4 = x_78;
x_7 = x_75;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_10);
lean_dec(x_5);
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2;
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
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_nullKind;
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_8);
x_12 = l_Lean_Syntax_isNodeOf(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1(x_6, x_16, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1(x_6, x_19, x_18);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optDeriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(2u);
lean_inc(x_10);
x_13 = l_Lean_Syntax_isNodeOf(x_10, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_2);
x_14 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_10, x_16);
lean_dec(x_10);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_9, x_19);
if (x_20 == 0)
{
lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_18);
x_54 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_21 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_19, x_19);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_19);
lean_dec(x_18);
x_56 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_21 = x_56;
goto block_53;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_59 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3;
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_18, x_57, x_58, x_59);
lean_dec(x_18);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_21 = x_61;
goto block_53;
}
}
block_53:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4;
x_23 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_21, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = x_26;
lean_inc(x_30);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_28, x_29, x_30);
x_32 = x_31;
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_28, x_29, x_30);
x_34 = x_33;
x_35 = lean_array_get_size(x_32);
x_36 = l_Array_toSubarray___rarg(x_32, x_9, x_35);
x_37 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_get_size(x_34);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3(x_34, x_40, x_29, x_38, x_2, x_3, x_4);
lean_dec(x_34);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected declarations must be in a namespace");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_2);
x_12 = l_Lean_Name_append(x_1, x_2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_5);
x_14 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__16(x_13, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(x_13);
if (lean_obj_tag(x_15) == 1)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_18);
x_21 = l_Lean_Name_append(x_20, x_2);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_name_mk_string(x_26, x_25);
x_28 = l_Lean_Name_append(x_27, x_2);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2;
x_33 = l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("atomic identifier expected '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_11 = l_Lean_extractMacroScopes(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Name_isAtomic(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Elab_isFreshInstanceName(x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1(x_1, x_3, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1(x_1, x_3, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe level named '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = l_Lean_Syntax_getId(x_13);
x_15 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_4);
x_17 = 1;
x_18 = x_2 + x_17;
x_2 = x_18;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_9, 3);
x_22 = l_Lean_replaceRef(x_13, x_21);
lean_dec(x_21);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_22);
x_23 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
x_30 = lean_ctor_get(x_9, 2);
x_31 = lean_ctor_get(x_9, 3);
x_32 = lean_ctor_get(x_9, 4);
x_33 = lean_ctor_get(x_9, 5);
x_34 = lean_ctor_get(x_9, 6);
x_35 = lean_ctor_get(x_9, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_36 = l_Lean_replaceRef(x_13, x_31);
lean_dec(x_31);
lean_dec(x_13);
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
x_38 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7(x_14, x_5, x_6, x_7, x_8, x_37, x_10, x_11);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 2);
x_16 = lean_ctor_get(x_10, 3);
x_17 = lean_ctor_get(x_10, 4);
x_18 = lean_ctor_get(x_10, 5);
x_19 = lean_ctor_get(x_10, 6);
x_20 = lean_ctor_get(x_10, 7);
x_21 = l_Lean_replaceRef(x_1, x_16);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_inc(x_6);
x_23 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_22, x_11, x_12);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_26);
x_29 = l_Lean_addDocString_x27___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__18(x_26, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_5);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Elab_expandDeclIdCore(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_14, x_16);
lean_dec(x_14);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_39; 
lean_dec(x_19);
lean_dec(x_18);
x_39 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_22 = x_39;
goto block_38;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_19, x_19);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_19);
lean_dec(x_18);
x_41 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_22 = x_41;
goto block_38;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_44 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3;
x_45 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_18, x_42, x_43, x_44);
lean_dec(x_18);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_22 = x_46;
goto block_38;
}
}
block_38:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_lt(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
x_25 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(x_3, x_1, x_4, x_13, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_27 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(x_3, x_1, x_4, x_13, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_23);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_5);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9(x_22, x_28, x_29, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(x_3, x_1, x_4, x_13, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_9);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_14);
x_47 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(x_3, x_1, x_4, x_13, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_47;
}
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("example");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
x_10 = l_Lean_Syntax_getKind(x_2);
x_11 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_getDeclarationSelectionRef(x_2);
x_17 = l_Lean_Elab_getDeclarationRange___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__21(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_addDeclarationRanges___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__22(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_3 == x_4;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
lean_inc(x_1);
x_12 = lean_array_push(x_11, x_1);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Elab_DerivingClassView_applyHandlers(x_10, x_12, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_3 + x_16;
x_3 = x_17;
x_5 = x_14;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_22 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_20, x_20, x_21, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_13);
x_24 = l_Lean_Elab_Term_addAutoBoundImplicits(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getLevelNames___rarg(x_14, x_15, x_16, x_17, x_18, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_5);
x_30 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_5);
lean_ctor_set(x_30, 5, x_6);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_7);
lean_ctor_set(x_30, 8, x_8);
lean_ctor_set(x_30, 9, x_9);
lean_ctor_set(x_30, 10, x_10);
lean_ctor_set_uint8(x_30, sizeof(void*)*11, x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_31 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView(x_30, x_13, x_14, x_15, x_16, x_17, x_18, x_29);
if (lean_obj_tag(x_31) == 0)
{
if (x_11 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_5);
x_33 = l_Lean_Meta_mkSizeOfInstances(x_5, x_15, x_16, x_17, x_18, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_5);
x_35 = l_Lean_Meta_mkInjectiveTheorems(x_5, x_15, x_16, x_17, x_18, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_5);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_31, 0);
lean_dec(x_49);
lean_ctor_set(x_31, 0, x_5);
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
return x_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_31, 0);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_31);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_24);
if (x_56 == 0)
{
return x_24;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_22);
if (x_60 == 0)
{
return x_22;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_22, 0);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_22);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor(x_1, x_2, x_3, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_12);
x_22 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields(x_1, x_2, x_3, x_12, x_13, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(x_5);
x_26 = lean_box(x_9);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__1___boxed), 19, 11);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_4);
lean_closure_set(x_27, 3, x_25);
lean_closure_set(x_27, 4, x_3);
lean_closure_set(x_27, 5, x_6);
lean_closure_set(x_27, 6, x_7);
lean_closure_set(x_27, 7, x_8);
lean_closure_set(x_27, 8, x_20);
lean_closure_set(x_27, 9, x_23);
lean_closure_set(x_27, 10, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_28, 0, x_10);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Term_withLevelNames___rarg(x_11, x_29, x_12, x_13, x_14, x_15, x_16, x_17, x_24);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Elab_Term_getLevelNames___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
lean_inc(x_14);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_18);
x_21 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4(x_20, x_18, x_1, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_3);
lean_inc(x_24);
x_26 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10(x_24, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(x_4);
x_29 = lean_box(x_8);
lean_inc(x_24);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__2___boxed), 18, 11);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_24);
lean_closure_set(x_30, 3, x_18);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_5);
lean_closure_set(x_30, 6, x_6);
lean_closure_set(x_30, 7, x_7);
lean_closure_set(x_30, 8, x_29);
lean_closure_set(x_30, 9, x_9);
lean_closure_set(x_30, 10, x_25);
x_31 = l_Lean_Elab_Term_withDeclName___rarg(x_24, x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_18, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_array_get_size(x_10);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_25 = l_Array_toSubarray___rarg(x_10, x_24, x_23);
x_26 = lean_ctor_get(x_1, 6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_array_get_size(x_26);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_26, x_29, x_30, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_21);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_11, 7);
lean_dec(x_36);
lean_ctor_set(x_11, 7, x_34);
x_37 = l_Lean_Elab_Term_resetMessageLog(x_11, x_12, x_13, x_14, x_15, x_16, x_33);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_13);
lean_inc(x_11);
x_39 = l_Lean_Elab_Term_addAutoBoundImplicits(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_38);
lean_dec(x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(x_5);
x_43 = lean_box(x_8);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__3___boxed), 16, 9);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_3);
lean_closure_set(x_44, 2, x_4);
lean_closure_set(x_44, 3, x_42);
lean_closure_set(x_44, 4, x_40);
lean_closure_set(x_44, 5, x_6);
lean_closure_set(x_44, 6, x_7);
lean_closure_set(x_44, 7, x_43);
lean_closure_set(x_44, 8, x_9);
x_45 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_41);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
x_52 = lean_ctor_get(x_11, 2);
x_53 = lean_ctor_get(x_11, 3);
x_54 = lean_ctor_get(x_11, 4);
x_55 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
x_56 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 1);
x_57 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 2);
x_58 = lean_ctor_get(x_11, 5);
x_59 = lean_ctor_get(x_11, 6);
x_60 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_61 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_61, 7, x_34);
lean_ctor_set_uint8(x_61, sizeof(void*)*8, x_55);
lean_ctor_set_uint8(x_61, sizeof(void*)*8 + 1, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*8 + 2, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*8 + 3, x_60);
x_62 = l_Lean_Elab_Term_resetMessageLog(x_61, x_12, x_13, x_14, x_15, x_16, x_33);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_13);
lean_inc(x_61);
x_64 = l_Lean_Elab_Term_addAutoBoundImplicits(x_10, x_61, x_12, x_13, x_14, x_15, x_16, x_63);
lean_dec(x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(x_5);
x_68 = lean_box(x_8);
x_69 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__3___boxed), 16, 9);
lean_closure_set(x_69, 0, x_2);
lean_closure_set(x_69, 1, x_3);
lean_closure_set(x_69, 2, x_4);
lean_closure_set(x_69, 3, x_67);
lean_closure_set(x_69, 4, x_65);
lean_closure_set(x_69, 5, x_6);
lean_closure_set(x_69, 6, x_7);
lean_closure_set(x_69, 7, x_68);
lean_closure_set(x_69, 8, x_9);
x_70 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_69, x_61, x_12, x_13, x_14, x_15, x_16, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_20);
if (x_75 == 0)
{
return x_20;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_20, 0);
x_77 = lean_ctor_get(x_20, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_20);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Command_getScope___rarg(x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 5);
lean_inc(x_17);
x_18 = lean_box(x_4);
x_19 = lean_box(x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__4___boxed), 17, 9);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_9);
lean_closure_set(x_20, 7, x_19);
lean_closure_set(x_20, 8, x_7);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_10);
x_23 = l_Lean_Elab_Command_liftTermElabM___rarg(x_13, x_22, x_10, x_11, x_16);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_array_get_size(x_8);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_30 = lean_box(0);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_32 = lean_box(0);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_23);
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11(x_25, x_8, x_33, x_34, x_35, x_10, x_11, x_26);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_array_get_size(x_8);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_39, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11(x_37, x_8, x_47, x_48, x_49, x_10, x_11, x_38);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("classTk");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sort");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6;
x_2 = l_Lean_Elab_Command_elabStructure___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Sort");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4;
x_2 = l_Lean_Elab_Command_elabStructure___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabStructure___closed__7;
x_2 = l_Lean_Elab_Command_elabStructure___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_Elab_Command_elabStructure___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Syntax_getArg(x_2, x_21);
x_23 = lean_unsigned_to_nat(6u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
lean_inc(x_3);
x_25 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(x_24, x_3, x_4, x_7);
if (x_12 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_26 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = 1;
x_26 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_1;
goto block_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Lean_Elab_Command_elabStructure___closed__10;
x_78 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_77);
x_27 = x_78;
goto block_76;
}
block_76:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
if (x_20 == 0)
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_25, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_25, 1);
lean_inc(x_61);
lean_dec(x_25);
x_62 = l_Lean_Syntax_getArg(x_19, x_8);
lean_dec(x_19);
x_63 = l_Lean_Syntax_getArg(x_62, x_13);
lean_dec(x_62);
x_64 = l_Lean_Syntax_getSepArgs(x_63);
lean_dec(x_63);
x_28 = x_64;
x_29 = x_60;
x_30 = x_61;
goto block_59;
}
else
{
uint8_t x_65; 
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_dec(x_25);
x_71 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1;
x_28 = x_71;
x_29 = x_69;
x_30 = x_70;
goto block_59;
}
else
{
uint8_t x_72; 
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_25);
if (x_72 == 0)
{
return x_25;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_25, 0);
x_74 = lean_ctor_get(x_25, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_25);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
block_59:
{
uint8_t x_31; 
x_31 = l_Lean_Syntax_isNone(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Syntax_getArg(x_22, x_8);
lean_dec(x_22);
x_33 = l_Lean_Syntax_getArg(x_32, x_13);
lean_dec(x_32);
x_34 = l_Lean_Elab_Command_elabStructure___lambda__5(x_14, x_27, x_2, x_12, x_28, x_26, x_17, x_29, x_33, x_3, x_4, x_30);
lean_dec(x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_22);
x_35 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfConstant___spec__1(x_3, x_4, x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_elabStructure___closed__5;
lean_inc(x_36);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1;
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4;
x_47 = lean_array_push(x_46, x_45);
x_48 = l_Lean_Elab_Command_elabStructure___closed__9;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_46, x_49);
x_51 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15;
x_54 = lean_array_push(x_53, x_43);
x_55 = lean_array_push(x_54, x_52);
x_56 = l_Lean_Elab_Command_elabStructure___closed__4;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Command_elabStructure___lambda__5(x_14, x_27, x_2, x_12, x_28, x_26, x_17, x_29, x_57, x_3, x_4, x_41);
lean_dec(x_29);
return x_58;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_6);
if (x_82 == 0)
{
return x_6;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get(x_6, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_6);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabStructure___spec__3(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabStructure___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_elabStructure___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabStructure___spec__11(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox(x_11);
lean_dec(x_11);
x_22 = l_Lean_Elab_Command_elabStructure___lambda__1(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_12);
return x_22;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Elab_Command_elabStructure___lambda__2(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l_Lean_Elab_Command_elabStructure___lambda__3(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_19;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__4___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l_Lean_Elab_Command_elabStructure___lambda__4(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_1);
return x_20;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Elab_Command_elabStructure___lambda__5(x_1, x_2, x_3, x_13, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Structure___hyg_5182_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_Meta_Closure(lean_object*);
lean_object* initialize_Lean_Meta_SizeOf(lean_object*);
lean_object* initialize_Lean_Meta_Injective(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Structure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SizeOf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedStructFieldKind = _init_l_Lean_Elab_Command_instInhabitedStructFieldKind();
l_Lean_Elab_Command_StructFieldInfo_inferMod___default = _init_l_Lean_Elab_Command_StructFieldInfo_inferMod___default();
l_Lean_Elab_Command_StructFieldInfo_value_x3f___default = _init_l_Lean_Elab_Command_StructFieldInfo_value_x3f___default();
lean_mark_persistent(l_Lean_Elab_Command_StructFieldInfo_value_x3f___default);
l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__1 = _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__1();
l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2 = _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__2);
l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3 = _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedStructFieldInfo___closed__3);
l_Lean_Elab_Command_instInhabitedStructFieldInfo = _init_l_Lean_Elab_Command_instInhabitedStructFieldInfo();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedStructFieldInfo);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_defaultCtorName);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__8___rarg___closed__1);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__1);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__2);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__3);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___lambda__2___closed__4);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__1);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__2);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__3);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__4);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__5);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__6);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__7);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__8);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__9);
l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10 = _init_l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10();
lean_mark_persistent(l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__4___closed__10);
l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1 = _init_l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__3___closed__1);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__1);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__2);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__3);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__4);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__5);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__6);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__7);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___lambda__3___closed__8);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__1);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__2);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__3);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__1___closed__4);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__15___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__1___closed__4);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___lambda__2___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___spec__17___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___lambda__2___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandCtor___closed__3);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___lambda__4___closed__2);
l_Lean_Elab_Command_checkValidFieldModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__3);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__1___closed__4);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__2___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__3___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__3);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__4);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__5);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__6);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__7);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___lambda__4___closed__8);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__3);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__4);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__5);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___spec__3___closed__6);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__2();
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__3();
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_expandFields___closed__4();
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__3);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_checkParentIsStructure___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_findFieldInfo_x3f___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__3);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_processSubfields_loop___rarg___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withParents___rarg___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabFieldTypeValue___lambda__1___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__3);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__5);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__6);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__7);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__8);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__9);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__10);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__11);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__12);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__13);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__14);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__15);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__16);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__17);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__18);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__19);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__20);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__21);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__22);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__23);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_withFields___rarg___closed__24);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_getResultUniverse___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_removeUnused___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_levelMVarToParamAux___boxed__const__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_updateResultingUniverse___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_collectLevelParamsInStructure___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addCtorFields___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__3);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__5);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_mkAuxConstructions___closed__6);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___spec__2___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_addDefaults___boxed__const__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__5);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__4___closed__6);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___spec__10___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__1___boxed__const__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__2);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__3);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__4);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__5);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___lambda__2___closed__6);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__1);
l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2 = _init_l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_0__Lean_Elab_Command_elabStructureView___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__1___closed__4);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1___closed__2);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__1);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___lambda__2___closed__2);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__1);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__2);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__3);
l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4 = _init_l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2___closed__4);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___lambda__1___closed__2);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_elabStructure___spec__5___closed__2);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__1);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_elabStructure___spec__7___closed__2);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__1);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabStructure___spec__10___closed__2);
l_Lean_Elab_Command_elabStructure___closed__1 = _init_l_Lean_Elab_Command_elabStructure___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__1);
l_Lean_Elab_Command_elabStructure___closed__2 = _init_l_Lean_Elab_Command_elabStructure___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__2);
l_Lean_Elab_Command_elabStructure___closed__3 = _init_l_Lean_Elab_Command_elabStructure___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__3);
l_Lean_Elab_Command_elabStructure___closed__4 = _init_l_Lean_Elab_Command_elabStructure___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__4);
l_Lean_Elab_Command_elabStructure___closed__5 = _init_l_Lean_Elab_Command_elabStructure___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__5);
l_Lean_Elab_Command_elabStructure___closed__6 = _init_l_Lean_Elab_Command_elabStructure___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__6);
l_Lean_Elab_Command_elabStructure___closed__7 = _init_l_Lean_Elab_Command_elabStructure___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__7);
l_Lean_Elab_Command_elabStructure___closed__8 = _init_l_Lean_Elab_Command_elabStructure___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__8);
l_Lean_Elab_Command_elabStructure___closed__9 = _init_l_Lean_Elab_Command_elabStructure___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__9);
l_Lean_Elab_Command_elabStructure___closed__10 = _init_l_Lean_Elab_Command_elabStructure___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__10);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Structure___hyg_5182_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
