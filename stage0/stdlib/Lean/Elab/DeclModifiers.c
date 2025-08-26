// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: Lean.Structure Lean.Elab.Attributes Lean.DocString.Add Lean.Parser.Command Lean.Parser.Command
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclIdCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__2;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0;
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__3;
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__7;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedComputeKind;
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__31;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__13;
lean_object* l_Lean_Environment_header(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__27;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__24;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1;
static lean_object* l_Lean_Elab_expandDeclIdCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__4;
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclIdCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPartial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__8;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedModifiers___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___lam__0___boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_expandDeclIdCore___closed__2;
static lean_object* l_Lean_Elab_RecKind_noConfusion___redArg___closed__0;
static lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__21;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringModifiers___closed__0;
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__7;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__2;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__7___boxed(lean_object**);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__2;
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__0;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1;
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__3;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__23;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__25;
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedRecKind;
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__5;
lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__28;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPartial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object**);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__3___boxed(lean_object**);
static lean_object* l_Lean_Elab_Modifiers_filterAttrs___closed__0;
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__8;
static lean_object* l_Lean_Elab_mkDeclName___redArg___closed__3;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___redArg___closed__2;
static lean_object* l_Lean_Elab_mkDeclName___redArg___closed__1;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringModifiers___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_toCtorIdx(lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_addDocString_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__7(uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__6;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx(uint8_t);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__7;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__3;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__29;
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__32;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2;
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__5;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedVisibility;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__22;
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__0;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___redArg___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__17;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2;
static lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object*);
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__9;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__18;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__15;
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedModifiers___closed__1;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Modifiers_addFirstAttr___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__5;
static lean_object* l_Lean_Elab_expandDeclId___redArg___closed__2;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__33;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___redArg___closed__1;
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedModifiers;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t);
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__5;
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2;
x_4 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4;
x_3 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5;
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_pushInfoLeaf___redArg(x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(x_1);
lean_inc_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_mkConstWithLevelParams___redArg(x_2, x_4, x_5, x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_box(x_2);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
lean_closure_set(x_11, 4, x_6);
lean_closure_set(x_11, 5, x_8);
lean_closure_set(x_11, 6, x_7);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a non-private declaration '", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1;
x_7 = l_Lean_MessageData_ofConstName(x_1, x_2);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___redArg(x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = 1;
lean_inc(x_12);
x_14 = l_Lean_Environment_contains(x_3, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_2, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_17 = lean_box(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
x_19 = lean_apply_1(x_6, x_12);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a private declaration '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1;
x_9 = l_Lean_MessageData_ofConstName(x_1, x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___redArg(x_3, x_4, x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
lean_inc(x_2);
x_11 = l_Lean_mkPrivateName(x_1, x_2);
x_12 = 1;
lean_inc(x_11);
x_13 = l_Lean_Environment_contains(x_1, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_3, lean_box(0), x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_box(x_12);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_7);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_8);
x_19 = lean_apply_1(x_9, x_11);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a reserved name", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_23; uint8_t x_24; 
lean_inc(x_4);
x_23 = l_Lean_privateToUserName(x_4);
lean_inc_ref(x_9);
x_24 = lean_is_reserved_name(x_9, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
lean_inc(x_4);
x_25 = l_Lean_mkPrivateName(x_10, x_4);
x_26 = lean_is_reserved_name(x_9, x_25);
x_11 = x_26;
goto block_22;
}
else
{
lean_dec_ref(x_9);
x_11 = x_24;
goto block_22;
}
block_22:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1;
x_16 = l_Lean_MessageData_ofConstName(x_4, x_5);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___redArg(x_6, x_7, x_19);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_8);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1;
x_11 = l_Lean_MessageData_ofConstName(x_1, x_2);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___redArg(x_3, x_4, x_14);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec_ref(x_9);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1;
x_19 = l_Lean_MessageData_ofConstName(x_17, x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___redArg(x_3, x_4, x_22);
x_24 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_23, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_12 = 0;
x_13 = lean_box(x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Lean_Environment_setExporting(x_11, x_12);
lean_inc(x_6);
lean_inc_ref(x_14);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_15);
lean_inc(x_8);
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4), 8, 7);
lean_closure_set(x_16, 0, x_7);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_14);
lean_closure_set(x_16, 6, x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_17);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6), 10, 9);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_7);
lean_closure_set(x_18, 2, x_8);
lean_closure_set(x_18, 3, x_6);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_2);
lean_closure_set(x_18, 6, x_5);
lean_closure_set(x_18, 7, x_17);
lean_closure_set(x_18, 8, x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_box(x_12);
lean_inc_ref(x_15);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_19);
lean_inc(x_6);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___boxed), 10, 9);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_7);
lean_closure_set(x_21, 4, x_20);
lean_closure_set(x_21, 5, x_2);
lean_closure_set(x_21, 6, x_5);
lean_closure_set(x_21, 7, x_19);
lean_closure_set(x_21, 8, x_15);
x_22 = 1;
lean_inc(x_7);
lean_inc_ref(x_15);
x_23 = l_Lean_Environment_contains(x_15, x_7, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_9);
lean_closure_set(x_24, 2, x_21);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_8, lean_box(0), x_25);
x_27 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_24);
x_28 = l_Lean_withEnv___redArg(x_2, x_10, x_4, x_15, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_inc(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(x_29, 0, x_6);
lean_closure_set(x_29, 1, x_9);
lean_closure_set(x_29, 2, x_21);
x_30 = lean_box(x_22);
lean_inc_ref(x_29);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
lean_inc(x_7);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___boxed), 8, 7);
lean_closure_set(x_31, 0, x_7);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_5);
lean_closure_set(x_31, 4, x_6);
lean_closure_set(x_31, 5, x_29);
lean_closure_set(x_31, 6, x_29);
lean_inc(x_6);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_32 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
x_33 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_32, x_31);
x_34 = l_Lean_withEnv___redArg(x_2, x_10, x_4, x_15, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9), 11, 10);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_8);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_11);
lean_closure_set(x_12, 8, x_9);
lean_closure_set(x_12, 9, x_4);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_checkNotAlreadyDeclared___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_Visibility_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Visibility_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_Visibility_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Visibility_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Visibility_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Visibility_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Elab_Visibility_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Elab_Visibility_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("regular", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("public", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_instToStringVisibility___lam__0___closed__0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_instToStringVisibility___lam__0___closed__1;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Elab_instToStringVisibility___lam__0___closed__2;
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToStringVisibility___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_instToStringVisibility___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t x_1) {
_start:
{
if (x_1 == 1)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_Visibility_isPrivate(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t x_1) {
_start:
{
if (x_1 == 2)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_Visibility_isPublic(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_7 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Environment_header(x_1);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 4);
lean_dec_ref(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
x_3 = x_12;
goto block_6;
}
else
{
goto block_9;
}
}
else
{
goto block_9;
}
block_6:
{
uint8_t x_4; 
x_4 = l_Lean_Elab_Visibility_isPrivate(x_2);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
block_9:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Elab_Visibility_isPublic(x_2);
return x_8;
}
else
{
x_3 = x_7;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Elab_Visibility_isInferredPublic(x_1, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_RecKind_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_RecKind_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_RecKind_toCtorIdx(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_RecKind_noConfusion___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Visibility_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_RecKind_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_RecKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Elab_RecKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Elab_RecKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_ComputeKind_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_ComputeKind_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Elab_ComputeKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_RecKind_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_ComputeKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Elab_ComputeKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Elab_ComputeKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Modifiers_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Modifiers_toCtorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedModifiers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedModifiers___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_instInhabitedModifiers___closed__0;
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = 0;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 3, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 4, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedModifiers() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedModifiers___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_3 = l_Lean_Elab_Visibility_isPrivate(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isPrivate(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_3 = l_Lean_Elab_Visibility_isPublic(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isPublic(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_4 = l_Lean_Elab_Visibility_isInferredPublic(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Modifiers_isInferredPublic(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isPartial(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPartial(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
if (x_2 == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPartial___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isInferredPartial(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
if (x_2 == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isNonrec(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
if (x_2 == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isMeta(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
if (x_2 == 2)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isNoncomputable(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_14 = lean_array_push(x_13, x_2);
x_15 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_12);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_Modifiers_addFirstAttr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Elab_Modifiers_addFirstAttr___closed__0;
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Array_append___redArg(x_6, x_4);
lean_dec_ref(x_4);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_16 = l_Lean_Elab_Modifiers_addFirstAttr___closed__0;
x_17 = lean_array_push(x_16, x_2);
x_18 = l_Array_append___redArg(x_17, x_15);
lean_dec_ref(x_15);
x_19 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 2, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 3, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 4, x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_12);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Modifiers_filterAttrs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = l_Lean_Elab_Modifiers_filterAttrs___closed__0;
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0(x_2, x_4, x_10, x_11, x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_1, 2, x_12);
return x_1;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = l_Lean_Elab_Modifiers_filterAttrs___closed__0;
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_2);
x_25 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 3, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 4, x_19);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_2);
x_27 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 3, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 4, x_19);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0(x_2, x_20, x_28, x_29, x_23);
lean_dec_ref(x_20);
x_31 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_16);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 2, x_17);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 3, x_18);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 4, x_19);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Modifiers_filterAttrs_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("local ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scoped ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
switch (x_2) {
case 0:
{
lean_object* x_33; 
x_33 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__1;
x_5 = x_33;
goto block_32;
}
case 1:
{
lean_object* x_34; 
x_34 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__7;
x_5 = x_34;
goto block_32;
}
default: 
{
lean_object* x_35; 
x_35 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__8;
x_5 = x_35;
goto block_32;
}
}
block_32:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_6 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__2;
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_3, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_box(0);
x_16 = 0;
x_17 = l_Lean_Syntax_formatStx(x_4, x_15, x_16);
x_18 = lean_unsigned_to_nat(120u);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_format_pretty(x_17, x_18, x_19, x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
x_24 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__4;
x_25 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__5;
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__6;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = 0;
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsafe", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nonrec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noncomputable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protected", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToStringVisibility___lam__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToStringVisibility___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/--", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__30;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-/", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__32;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_29; lean_object* x_30; lean_object* x_35; lean_object* x_36; lean_object* x_42; lean_object* x_43; lean_object* x_49; lean_object* x_50; lean_object* x_55; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_55 = x_60;
goto block_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec_ref(x_4);
x_62 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__31;
x_63 = lean_box(0);
x_64 = 0;
x_65 = l_Lean_Syntax_formatStx(x_61, x_63, x_64);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__33;
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_55 = x_70;
goto block_59;
}
block_28:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_13 = l_List_appendTR___redArg(x_11, x_12);
x_14 = lean_array_to_list(x_10);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___redArg(x_1, x_14, x_15);
x_17 = l_List_appendTR___redArg(x_13, x_16);
x_18 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__3;
x_19 = l_Std_Format_joinSep___redArg(x_2, x_17, x_18);
x_20 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__5;
x_21 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__6;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__7;
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
return x_27;
}
block_34:
{
lean_object* x_31; 
x_31 = l_List_appendTR___redArg(x_29, x_30);
if (x_9 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_11 = x_31;
x_12 = x_32;
goto block_28;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__10;
x_11 = x_31;
x_12 = x_33;
goto block_28;
}
}
block_41:
{
lean_object* x_37; 
x_37 = l_List_appendTR___redArg(x_35, x_36);
switch (x_8) {
case 0:
{
lean_object* x_38; 
x_38 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__13;
x_29 = x_37;
x_30 = x_38;
goto block_34;
}
case 1:
{
lean_object* x_39; 
x_39 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__16;
x_29 = x_37;
x_30 = x_39;
goto block_34;
}
default: 
{
lean_object* x_40; 
x_40 = lean_box(0);
x_29 = x_37;
x_30 = x_40;
goto block_34;
}
}
}
block_48:
{
lean_object* x_44; 
x_44 = l_List_appendTR___redArg(x_42, x_43);
switch (x_7) {
case 0:
{
lean_object* x_45; 
x_45 = lean_box(0);
x_35 = x_44;
x_36 = x_45;
goto block_41;
}
case 1:
{
lean_object* x_46; 
x_46 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__19;
x_35 = x_44;
x_36 = x_46;
goto block_41;
}
default: 
{
lean_object* x_47; 
x_47 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__22;
x_35 = x_44;
x_36 = x_47;
goto block_41;
}
}
}
block_54:
{
lean_object* x_51; 
x_51 = l_List_appendTR___redArg(x_49, x_50);
if (x_6 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_42 = x_51;
x_43 = x_52;
goto block_48;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__25;
x_42 = x_51;
x_43 = x_53;
goto block_48;
}
}
block_59:
{
switch (x_5) {
case 0:
{
lean_object* x_56; 
x_56 = lean_box(0);
x_49 = x_55;
x_50 = x_56;
goto block_54;
}
case 1:
{
lean_object* x_57; 
x_57 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__27;
x_49 = x_55;
x_50 = x_57;
goto block_54;
}
default: 
{
lean_object* x_58; 
x_58 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__29;
x_49 = x_55;
x_50 = x_58;
goto block_54;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_instToFormatFormat___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToFormatModifiers___lam__0), 1, 0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instToFormatModifiers___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(120u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToFormatModifiers___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__0;
x_2 = l_Lean_Elab_instToStringModifiers___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instToFormatModifiers___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToStringModifiers___lam__0), 1, 0);
x_2 = l_Lean_Elab_instToStringModifiers___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_1);
lean_closure_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected doc string", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
x_6 = l_Lean_Syntax_getOptional_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_10, x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_string_utf8_extract(x_13, x_14, x_17);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_ctor_set(x_6, 0, x_18);
x_19 = lean_apply_2(x_5, lean_box(0), x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_6);
x_20 = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1;
x_21 = l_Lean_MessageData_ofSyntax(x_12);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_10, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Syntax_getArg(x_27, x_28);
if (lean_obj_tag(x_29) == 2)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_string_utf8_byte_size(x_30);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = lean_string_utf8_extract(x_30, x_31, x_34);
lean_dec(x_34);
lean_dec_ref(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_apply_2(x_5, lean_box(0), x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1;
x_39 = l_Lean_MessageData_ofSyntax(x_29);
x_40 = l_Lean_indentD(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_27, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandOptDocComment_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_expandOptDocComment_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandOptDocComment_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_14; 
x_14 = l_Lean_Syntax_isNone(x_8);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
x_10 = x_15;
goto block_13;
}
else
{
uint8_t x_16; 
x_16 = 0;
x_10 = x_16;
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 2, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 3, x_6);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 4, x_10);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22) {
_start:
{
uint8_t x_23; uint8_t x_39; 
x_39 = l_Lean_Syntax_isNone(x_21);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 1;
x_23 = x_40;
goto block_38;
}
else
{
uint8_t x_41; 
x_41 = 0;
x_23 = x_41;
goto block_38;
}
block_38:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_box(x_22);
x_25 = lean_box(x_23);
x_26 = lean_box(x_3);
x_27 = lean_box(x_4);
lean_inc(x_5);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_24);
lean_closure_set(x_28, 3, x_25);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_6);
x_29 = l_Lean_Syntax_getOptional_x3f(x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(x_30, 0, x_28);
x_31 = lean_mk_empty_array_with_capacity(x_8);
x_32 = lean_apply_2(x_5, lean_box(0), x_31);
x_33 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_32, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec_ref(x_29);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(x_35, 0, x_28);
x_36 = l_Lean_Elab_elabDeclAttrs___redArg(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_34);
lean_dec(x_34);
x_37 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_36, x_35);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instToStringVisibility___lam__0___closed__1;
x_2 = l_Lean_Elab_elabModifiers___redArg___closed__2;
x_3 = l_Lean_Elab_elabModifiers___redArg___closed__1;
x_4 = l_Lean_Elab_elabModifiers___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instToStringVisibility___lam__0___closed__2;
x_2 = l_Lean_Elab_elabModifiers___redArg___closed__2;
x_3 = l_Lean_Elab_elabModifiers___redArg___closed__1;
x_4 = l_Lean_Elab_elabModifiers___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected visibility modifier", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabModifiers___redArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__11;
x_2 = l_Lean_Elab_elabModifiers___redArg___closed__2;
x_3 = l_Lean_Elab_elabModifiers___redArg___closed__1;
x_4 = l_Lean_Elab_elabModifiers___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instToFormatModifiers___lam__1___closed__17;
x_2 = l_Lean_Elab_elabModifiers___redArg___closed__2;
x_3 = l_Lean_Elab_elabModifiers___redArg___closed__1;
x_4 = l_Lean_Elab_elabModifiers___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_57; lean_object* x_58; uint8_t x_59; uint8_t x_66; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_12, x_20);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_12, x_22);
x_80 = lean_unsigned_to_nat(4u);
x_81 = l_Lean_Syntax_getArg(x_12, x_80);
x_82 = l_Lean_Syntax_isNone(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = l_Lean_Syntax_getArg(x_81, x_16);
lean_dec(x_81);
x_84 = l_Lean_Syntax_getKind(x_83);
x_85 = l_Lean_Elab_elabModifiers___redArg___closed__8;
x_86 = lean_name_eq(x_84, x_85);
lean_dec(x_84);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = 2;
x_66 = x_87;
goto block_79;
}
else
{
uint8_t x_88; 
x_88 = 1;
x_66 = x_88;
goto block_79;
}
}
else
{
uint8_t x_89; 
lean_dec(x_81);
x_89 = 0;
x_66 = x_89;
goto block_79;
}
block_56:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_box(x_24);
x_29 = lean_box(x_26);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
lean_inc(x_14);
lean_inc(x_15);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 22, 21);
lean_closure_set(x_30, 0, x_12);
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_28);
lean_closure_set(x_30, 3, x_29);
lean_closure_set(x_30, 4, x_15);
lean_closure_set(x_30, 5, x_25);
lean_closure_set(x_30, 6, x_19);
lean_closure_set(x_30, 7, x_16);
lean_closure_set(x_30, 8, x_14);
lean_closure_set(x_30, 9, x_1);
lean_closure_set(x_30, 10, x_2);
lean_closure_set(x_30, 11, x_3);
lean_closure_set(x_30, 12, x_4);
lean_closure_set(x_30, 13, x_5);
lean_closure_set(x_30, 14, x_6);
lean_closure_set(x_30, 15, x_7);
lean_closure_set(x_30, 16, x_8);
lean_closure_set(x_30, 17, x_9);
lean_closure_set(x_30, 18, x_10);
lean_closure_set(x_30, 19, x_11);
lean_closure_set(x_30, 20, x_23);
x_31 = l_Lean_Syntax_getOptional_x3f(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_apply_2(x_15, lean_box(0), x_34);
x_36 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_35, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec_ref(x_31);
x_38 = l_Lean_Elab_elabModifiers___redArg___closed__3;
lean_inc(x_37);
x_39 = l_Lean_Syntax_isOfKind(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Elab_elabModifiers___redArg___closed__4;
lean_inc(x_37);
x_41 = l_Lean_Syntax_isOfKind(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_42, 0, x_30);
x_43 = l_Lean_Elab_elabModifiers___redArg___closed__6;
x_44 = l_Lean_throwErrorAt___redArg(x_1, x_4, x_37, x_43);
x_45 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_44, x_42);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_inc(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_46, 0, x_30);
x_47 = 2;
x_48 = lean_box(x_47);
x_49 = lean_apply_2(x_15, lean_box(0), x_48);
x_50 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_49, x_46);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_inc(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_51, 0, x_30);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_apply_2(x_15, lean_box(0), x_53);
x_55 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_54, x_51);
return x_55;
}
}
}
block_65:
{
lean_object* x_60; 
x_60 = l_Lean_Syntax_getOptional_x3f(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_61;
goto block_56;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_60;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_64;
goto block_56;
}
}
}
block_79:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_unsigned_to_nat(5u);
x_68 = l_Lean_Syntax_getArg(x_12, x_67);
x_69 = lean_unsigned_to_nat(6u);
x_70 = l_Lean_Syntax_getArg(x_12, x_69);
x_71 = l_Lean_Syntax_isNone(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Lean_Syntax_getArg(x_70, x_16);
lean_dec(x_70);
x_73 = l_Lean_Syntax_getKind(x_72);
x_74 = l_Lean_Elab_elabModifiers___redArg___closed__7;
x_75 = lean_name_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = 1;
x_57 = x_66;
x_58 = x_68;
x_59 = x_76;
goto block_65;
}
else
{
uint8_t x_77; 
x_77 = 0;
x_57 = x_66;
x_58 = x_68;
x_59 = x_77;
goto block_65;
}
}
else
{
uint8_t x_78; 
lean_dec(x_70);
x_78 = 2;
x_57 = x_66;
x_58 = x_68;
x_59 = x_78;
goto block_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_elabModifiers___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Elab_elabModifiers___redArg___lam__0(x_1, x_2, x_10, x_11, x_12, x_13, x_7, x_8, x_9);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_3);
x_24 = lean_unbox(x_4);
x_25 = lean_unbox(x_22);
x_26 = l_Lean_Elab_elabModifiers___redArg___lam__3(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_25);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Elab_elabModifiers___redArg___lam__2(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_addProtected(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_apply_1(x_5, x_6);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2), 2, 1);
lean_closure_set(x_13, 0, x_10);
lean_inc_ref(x_12);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_12);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___redArg(x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_mkPrivateName(x_5, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = l_Lean_Elab_Visibility_isInferredPublic(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_5, lean_box(0), x_11);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_9);
lean_inc_ref(x_6);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_1);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_3);
lean_closure_set(x_13, 7, x_4);
lean_closure_set(x_13, 8, x_5);
lean_inc(x_9);
lean_inc(x_12);
lean_inc_ref(x_13);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_14, 0, x_7);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_7);
lean_inc(x_10);
lean_inc(x_9);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_10);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_12);
lean_closure_set(x_16, 5, x_15);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_applyVisibility___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_applyVisibility___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_applyVisibility___redArg___lam__5(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_applyVisibility___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid declaration name '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', structure '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has field '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_Name_append(x_1, x_10);
x_14 = lean_name_eq(x_13, x_2);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_2(x_3, lean_box(0), x_4);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_3);
x_17 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1;
x_18 = 0;
x_19 = l_Lean_MessageData_ofConstName(x_2, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_ofName(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofName(x_10);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___redArg(x_7, x_8, x_30);
x_32 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_31, x_9);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_9 = l_Lean_getStructureFieldsFlattened(x_8, x_1, x_2);
x_10 = lean_box(0);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_3);
lean_inc_ref(x_6);
lean_inc_ref(x_11);
lean_inc(x_5);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 12, 9);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_11);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_10);
x_14 = lean_array_size(x_9);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_12, x_14, x_15, x_10);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc(x_1);
x_9 = l_Lean_isStructure(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_9);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
lean_inc(x_9);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 8, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_6);
lean_closure_set(x_10, 4, x_1);
lean_closure_set(x_10, 5, x_3);
lean_closure_set(x_10, 6, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkIfShadowingStructureField___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protected declarations must be in a namespace", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_13 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_box(0);
x_16 = l_Lean_Name_str___override(x_15, x_13);
x_17 = l_Lean_Name_append(x_16, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_apply_2(x_14, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_8);
lean_closure_set(x_20, 2, x_3);
x_21 = l_Lean_Name_isAtomic(x_3);
lean_dec(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(x_23, 0, x_20);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_22, lean_box(0), x_24);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_25, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(x_27, 0, x_20);
x_28 = l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1;
x_29 = l_Lean_throwError___redArg(x_6, x_7, x_28);
x_30 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_29, x_27);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_applyVisibility___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_5);
lean_inc(x_3);
lean_inc(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_7);
lean_closure_set(x_14, 4, x_8);
lean_closure_set(x_14, 5, x_1);
lean_closure_set(x_14, 6, x_9);
lean_closure_set(x_14, 7, x_3);
lean_closure_set(x_14, 8, x_13);
x_15 = l_Lean_Elab_checkIfShadowingStructureField___redArg(x_4, x_6, x_5, x_9);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
if (x_9 == 0)
{
lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_inc(x_16);
lean_inc(x_15);
x_44 = l_Lean_Name_append(x_15, x_16);
x_18 = x_44;
goto block_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_box(0);
lean_inc(x_10);
x_46 = l_Lean_Name_replacePrefix(x_10, x_11, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_13);
lean_ctor_set(x_47, 3, x_14);
x_48 = l_Lean_MacroScopesView_review(x_47);
x_18 = x_48;
goto block_43;
}
block_43:
{
lean_object* x_19; 
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2), 12, 9);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
lean_closure_set(x_19, 8, x_18);
if (x_9 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec_ref(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_20, lean_box(0), x_22);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_21);
return x_24;
}
else
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_10);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec_ref(x_2);
x_28 = lean_box(0);
x_29 = l_Lean_Name_str___override(x_28, x_26);
x_30 = l_Lean_Name_replacePrefix(x_25, x_11, x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(x_31, 0, x_19);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_29);
x_32 = lean_box(0);
x_33 = lean_apply_2(x_27, lean_box(0), x_32);
x_34 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_33, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_2);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(x_35, 0, x_19);
lean_closure_set(x_35, 1, x_15);
lean_closure_set(x_35, 2, x_16);
x_36 = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1;
x_37 = l_Lean_MessageData_ofName(x_10);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___redArg(x_4, x_5, x_40);
x_42 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_41, x_35);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace", 93, 93);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_8);
x_9 = l_Lean_extractMacroScopes(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 3);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = l_Lean_Elab_mkDeclName___redArg___closed__1;
x_17 = l_Lean_Name_isPrefixOf(x_16, x_10);
x_18 = lean_box(x_17);
lean_inc(x_10);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_15);
lean_inc_ref(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__7___boxed), 17, 14);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_2);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_5);
lean_closure_set(x_19, 8, x_18);
lean_closure_set(x_19, 9, x_10);
lean_closure_set(x_19, 10, x_16);
lean_closure_set(x_19, 11, x_11);
lean_closure_set(x_19, 12, x_12);
lean_closure_set(x_19, 13, x_13);
x_20 = lean_name_eq(x_10, x_16);
lean_dec(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_8);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_21, lean_box(0), x_23);
x_25 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_6);
lean_closure_set(x_26, 2, x_8);
x_27 = l_Lean_Elab_mkDeclName___redArg___closed__3;
x_28 = l_Lean_throwError___redArg(x_1, x_3, x_27);
x_29 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_28, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_mkDeclName___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_mkDeclName___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__7___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_9);
x_19 = l_Lean_Elab_mkDeclName___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
return x_19;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclIdCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclIdCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclIdCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_expandDeclIdCore___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclIdCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_expandDeclIdCore___closed__0;
x_2 = l_Lean_Elab_expandDeclIdCore___closed__2;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getId(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Syntax_getId(x_1);
x_10 = l_Lean_Elab_expandDeclIdCore___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_expandDeclIdCore(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_ExpandDeclIdResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ExpandDeclIdResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_ExpandDeclIdResult_toCtorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__0), 5, 4);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
x_17 = l_Lean_addDocString_x27___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13, x_15);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__1), 12, 11);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_8);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_10);
lean_closure_set(x_20, 10, x_11);
x_21 = l_Lean_Elab_mkDeclName___redArg(x_4, x_6, x_5, x_12, x_13, x_14, x_2, x_15);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_21);
lean_inc(x_11);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_18, x_22);
x_24 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_23, x_20);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Syntax_getId(x_7);
x_9 = l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0;
lean_inc(x_6);
lean_inc(x_8);
x_10 = l_List_elem___redArg(x_9, x_8, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(x_3, x_4, x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__4___boxed), 4, 3);
lean_closure_set(x_16, 0, x_7);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__7(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_box(x_1);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_box(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_array_push(x_14, x_4);
x_17 = lean_box(x_2);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_array_push(x_18, x_4);
x_20 = lean_box(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandDeclId___redArg___closed__1;
x_2 = l_Lean_Elab_expandDeclId___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_expandDeclId___redArg___closed__5;
x_2 = l_Lean_Elab_expandDeclId___redArg___closed__4;
x_3 = l_Lean_Elab_expandDeclId___redArg___closed__3;
x_4 = l_Lean_Elab_expandDeclId___redArg___closed__2;
x_5 = l_Lean_Elab_expandDeclId___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandDeclId___redArg___closed__6;
x_2 = l_Lean_Elab_expandDeclId___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Elab_expandDeclIdCore(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_15);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_17);
lean_inc_ref(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__3___boxed), 17, 16);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_13);
lean_closure_set(x_22, 2, x_17);
lean_closure_set(x_22, 3, x_1);
lean_closure_set(x_22, 4, x_3);
lean_closure_set(x_22, 5, x_2);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_6);
lean_closure_set(x_22, 8, x_5);
lean_closure_set(x_22, 9, x_9);
lean_closure_set(x_22, 10, x_15);
lean_closure_set(x_22, 11, x_4);
lean_closure_set(x_22, 12, x_8);
lean_closure_set(x_22, 13, x_10);
lean_closure_set(x_22, 14, x_20);
lean_closure_set(x_22, 15, x_12);
x_23 = l_Lean_Syntax_isNone(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_15);
lean_inc_ref(x_1);
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__5), 7, 5);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_16);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_15);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__6), 2, 1);
lean_closure_set(x_25, 0, x_22);
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_21, x_40);
lean_dec(x_21);
x_42 = l_Lean_Syntax_getArgs(x_41);
lean_dec(x_41);
x_43 = l_Lean_Elab_expandDeclIdCore___closed__0;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_42);
x_46 = l_Lean_Elab_expandDeclId___redArg___closed__9;
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec_ref(x_42);
lean_free_object(x_18);
x_26 = x_43;
goto block_39;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
lean_dec(x_45);
lean_dec_ref(x_42);
lean_free_object(x_18);
x_26 = x_43;
goto block_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_box(x_48);
x_50 = lean_box(x_23);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_50);
x_52 = lean_box(x_48);
lean_ctor_set(x_18, 1, x_43);
lean_ctor_set(x_18, 0, x_52);
x_53 = 0;
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_46, x_51, x_42, x_53, x_54, x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_26 = x_56;
goto block_39;
}
}
block_39:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_inc(x_17);
lean_dec_ref(x_1);
x_30 = lean_apply_2(x_17, lean_box(0), x_11);
x_31 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_30, x_25);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_inc(x_17);
lean_dec_ref(x_1);
x_33 = lean_apply_2(x_17, lean_box(0), x_11);
x_34 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_33, x_25);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_24, x_26, x_35, x_36, x_11);
x_38 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_37, x_25);
return x_38;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_18);
lean_dec(x_21);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__6), 2, 1);
lean_closure_set(x_57, 0, x_22);
x_58 = lean_apply_2(x_17, lean_box(0), x_11);
x_59 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_58, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
lean_inc(x_15);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_17);
lean_inc_ref(x_16);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__3___boxed), 17, 16);
lean_closure_set(x_62, 0, x_16);
lean_closure_set(x_62, 1, x_13);
lean_closure_set(x_62, 2, x_17);
lean_closure_set(x_62, 3, x_1);
lean_closure_set(x_62, 4, x_3);
lean_closure_set(x_62, 5, x_2);
lean_closure_set(x_62, 6, x_7);
lean_closure_set(x_62, 7, x_6);
lean_closure_set(x_62, 8, x_5);
lean_closure_set(x_62, 9, x_9);
lean_closure_set(x_62, 10, x_15);
lean_closure_set(x_62, 11, x_4);
lean_closure_set(x_62, 12, x_8);
lean_closure_set(x_62, 13, x_10);
lean_closure_set(x_62, 14, x_60);
lean_closure_set(x_62, 15, x_12);
x_63 = l_Lean_Syntax_isNone(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_inc(x_15);
lean_inc_ref(x_1);
lean_inc(x_17);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__5), 7, 5);
lean_closure_set(x_64, 0, x_17);
lean_closure_set(x_64, 1, x_16);
lean_closure_set(x_64, 2, x_1);
lean_closure_set(x_64, 3, x_3);
lean_closure_set(x_64, 4, x_15);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__6), 2, 1);
lean_closure_set(x_65, 0, x_62);
x_80 = lean_unsigned_to_nat(1u);
x_81 = l_Lean_Syntax_getArg(x_61, x_80);
lean_dec(x_61);
x_82 = l_Lean_Syntax_getArgs(x_81);
lean_dec(x_81);
x_83 = l_Lean_Elab_expandDeclIdCore___closed__0;
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_82);
x_86 = l_Lean_Elab_expandDeclId___redArg___closed__9;
x_87 = lean_nat_dec_lt(x_84, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_82);
x_66 = x_83;
goto block_79;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_82);
x_66 = x_83;
goto block_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_box(x_88);
x_90 = lean_box(x_63);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_90);
x_92 = lean_box(x_88);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_83);
x_94 = 0;
x_95 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_86, x_91, x_82, x_94, x_95, x_93);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_66 = x_97;
goto block_79;
}
}
block_79:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_array_get_size(x_66);
x_69 = lean_nat_dec_lt(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_68);
lean_dec_ref(x_66);
lean_dec_ref(x_64);
lean_inc(x_17);
lean_dec_ref(x_1);
x_70 = lean_apply_2(x_17, lean_box(0), x_11);
x_71 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_70, x_65);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_68, x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_68);
lean_dec_ref(x_66);
lean_dec_ref(x_64);
lean_inc(x_17);
lean_dec_ref(x_1);
x_73 = lean_apply_2(x_17, lean_box(0), x_11);
x_74 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_73, x_65);
return x_74;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_64, x_66, x_75, x_76, x_11);
x_78 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_77, x_65);
return x_78;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_61);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___redArg___lam__6), 2, 1);
lean_closure_set(x_98, 0, x_62);
x_99 = lean_apply_2(x_17, lean_box(0), x_11);
x_100 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_99, x_98);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_expandDeclId___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandDeclId___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__3___boxed(lean_object** _args) {
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
x_18 = l_Lean_Elab_expandDeclId___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandDeclId___redArg___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Elab_expandDeclId___redArg___lam__7(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__5);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__0);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__0);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__0);
l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__12___closed__1);
l_Lean_Elab_instInhabitedVisibility = _init_l_Lean_Elab_instInhabitedVisibility();
l_Lean_Elab_instToStringVisibility___lam__0___closed__0 = _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___lam__0___closed__0);
l_Lean_Elab_instToStringVisibility___lam__0___closed__1 = _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___lam__0___closed__1);
l_Lean_Elab_instToStringVisibility___lam__0___closed__2 = _init_l_Lean_Elab_instToStringVisibility___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___lam__0___closed__2);
l_Lean_Elab_instToStringVisibility = _init_l_Lean_Elab_instToStringVisibility();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility);
l_Lean_Elab_RecKind_noConfusion___redArg___closed__0 = _init_l_Lean_Elab_RecKind_noConfusion___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_RecKind_noConfusion___redArg___closed__0);
l_Lean_Elab_instInhabitedRecKind = _init_l_Lean_Elab_instInhabitedRecKind();
l_Lean_Elab_instInhabitedComputeKind = _init_l_Lean_Elab_instInhabitedComputeKind();
l_Lean_Elab_instInhabitedModifiers___closed__0 = _init_l_Lean_Elab_instInhabitedModifiers___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedModifiers___closed__0);
l_Lean_Elab_instInhabitedModifiers___closed__1 = _init_l_Lean_Elab_instInhabitedModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedModifiers___closed__1);
l_Lean_Elab_instInhabitedModifiers = _init_l_Lean_Elab_instInhabitedModifiers();
lean_mark_persistent(l_Lean_Elab_instInhabitedModifiers);
l_Lean_Elab_Modifiers_addFirstAttr___closed__0 = _init_l_Lean_Elab_Modifiers_addFirstAttr___closed__0();
lean_mark_persistent(l_Lean_Elab_Modifiers_addFirstAttr___closed__0);
l_Lean_Elab_Modifiers_filterAttrs___closed__0 = _init_l_Lean_Elab_Modifiers_filterAttrs___closed__0();
lean_mark_persistent(l_Lean_Elab_Modifiers_filterAttrs___closed__0);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__0 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__1 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__1);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__2 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__3 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__4 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__5 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__6 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__7 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7);
l_Lean_Elab_instToFormatModifiers___lam__0___closed__8 = _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__0___closed__8);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__0 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__1 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__1);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__2 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__3 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__4 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__4);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__5 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__6 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__7 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__7();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__8 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__8();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__9 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__9();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__9);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__10 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__10();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__10);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__11 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__11();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__12 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__12();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__12);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__13 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__13();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__13);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__14 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__14();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__15 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__15();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__15);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__16 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__16();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__16);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__17 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__17();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__18 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__18();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__18);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__19 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__19();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__19);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__20 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__20();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__21 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__21();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__21);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__22 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__22();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__22);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__23 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__23();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__24 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__24();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__24);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__25 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__25();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__25);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__26 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__26();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__27 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__27();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__27);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__28 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__28();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__29 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__29();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__29);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__30 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__30();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__31 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__31();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__31);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__32 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__32();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32);
l_Lean_Elab_instToFormatModifiers___lam__1___closed__33 = _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__33();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33);
l_Lean_Elab_instToFormatModifiers___closed__0 = _init_l_Lean_Elab_instToFormatModifiers___closed__0();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__0);
l_Lean_Elab_instToFormatModifiers = _init_l_Lean_Elab_instToFormatModifiers();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers);
l_Lean_Elab_instToStringModifiers___closed__0 = _init_l_Lean_Elab_instToStringModifiers___closed__0();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers___closed__0);
l_Lean_Elab_instToStringModifiers___closed__1 = _init_l_Lean_Elab_instToStringModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers___closed__1);
l_Lean_Elab_instToStringModifiers = _init_l_Lean_Elab_instToStringModifiers();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers);
l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0 = _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0);
l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1 = _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2 = _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2);
l_Lean_Elab_elabModifiers___redArg___closed__0 = _init_l_Lean_Elab_elabModifiers___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__0);
l_Lean_Elab_elabModifiers___redArg___closed__1 = _init_l_Lean_Elab_elabModifiers___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__1);
l_Lean_Elab_elabModifiers___redArg___closed__2 = _init_l_Lean_Elab_elabModifiers___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__2);
l_Lean_Elab_elabModifiers___redArg___closed__3 = _init_l_Lean_Elab_elabModifiers___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__3);
l_Lean_Elab_elabModifiers___redArg___closed__4 = _init_l_Lean_Elab_elabModifiers___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__4);
l_Lean_Elab_elabModifiers___redArg___closed__5 = _init_l_Lean_Elab_elabModifiers___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__5);
l_Lean_Elab_elabModifiers___redArg___closed__6 = _init_l_Lean_Elab_elabModifiers___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__6);
l_Lean_Elab_elabModifiers___redArg___closed__7 = _init_l_Lean_Elab_elabModifiers___redArg___closed__7();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__7);
l_Lean_Elab_elabModifiers___redArg___closed__8 = _init_l_Lean_Elab_elabModifiers___redArg___closed__8();
lean_mark_persistent(l_Lean_Elab_elabModifiers___redArg___closed__8);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4);
l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5 = _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5();
lean_mark_persistent(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0 = _init_l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___lam__3___closed__0);
l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1 = _init_l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___lam__3___closed__1);
l_Lean_Elab_mkDeclName___redArg___closed__0 = _init_l_Lean_Elab_mkDeclName___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___closed__0);
l_Lean_Elab_mkDeclName___redArg___closed__1 = _init_l_Lean_Elab_mkDeclName___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___closed__1);
l_Lean_Elab_mkDeclName___redArg___closed__2 = _init_l_Lean_Elab_mkDeclName___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___closed__2);
l_Lean_Elab_mkDeclName___redArg___closed__3 = _init_l_Lean_Elab_mkDeclName___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_mkDeclName___redArg___closed__3);
l_Lean_Elab_expandDeclIdCore___closed__0 = _init_l_Lean_Elab_expandDeclIdCore___closed__0();
lean_mark_persistent(l_Lean_Elab_expandDeclIdCore___closed__0);
l_Lean_Elab_expandDeclIdCore___closed__1 = _init_l_Lean_Elab_expandDeclIdCore___closed__1();
lean_mark_persistent(l_Lean_Elab_expandDeclIdCore___closed__1);
l_Lean_Elab_expandDeclIdCore___closed__2 = _init_l_Lean_Elab_expandDeclIdCore___closed__2();
lean_mark_persistent(l_Lean_Elab_expandDeclIdCore___closed__2);
l_Lean_Elab_expandDeclIdCore___closed__3 = _init_l_Lean_Elab_expandDeclIdCore___closed__3();
lean_mark_persistent(l_Lean_Elab_expandDeclIdCore___closed__3);
l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0 = _init_l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___lam__5___closed__0);
l_Lean_Elab_expandDeclId___redArg___closed__0 = _init_l_Lean_Elab_expandDeclId___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__0);
l_Lean_Elab_expandDeclId___redArg___closed__1 = _init_l_Lean_Elab_expandDeclId___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__1);
l_Lean_Elab_expandDeclId___redArg___closed__2 = _init_l_Lean_Elab_expandDeclId___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__2);
l_Lean_Elab_expandDeclId___redArg___closed__3 = _init_l_Lean_Elab_expandDeclId___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__3);
l_Lean_Elab_expandDeclId___redArg___closed__4 = _init_l_Lean_Elab_expandDeclId___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__4);
l_Lean_Elab_expandDeclId___redArg___closed__5 = _init_l_Lean_Elab_expandDeclId___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__5);
l_Lean_Elab_expandDeclId___redArg___closed__6 = _init_l_Lean_Elab_expandDeclId___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__6);
l_Lean_Elab_expandDeclId___redArg___closed__7 = _init_l_Lean_Elab_expandDeclId___redArg___closed__7();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__7);
l_Lean_Elab_expandDeclId___redArg___closed__8 = _init_l_Lean_Elab_expandDeclId___redArg___closed__8();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__8);
l_Lean_Elab_expandDeclId___redArg___closed__9 = _init_l_Lean_Elab_expandDeclId___redArg___closed__9();
lean_mark_persistent(l_Lean_Elab_expandDeclId___redArg___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
