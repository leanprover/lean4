// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: Init Lean.Modifiers Lean.DocString Lean.Elab.Attributes Lean.Elab.Exception Lean.Elab.DeclUtil
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringVisibility___closed__3;
static lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
size_t l_USize_add(size_t, size_t);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_addDocString_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__5;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedModifiers;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__18;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_instToStringModifiers___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedRecKind;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_instReprProd___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_docString_x3f___default;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility(uint8_t);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__8;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__23;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable___default;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___rarg___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__21;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__13;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1;
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_recKind___default;
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__9;
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__17;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__4;
static lean_object* l_Lean_Elab_instToStringModifiers___closed__2;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lambda__1(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__11;
extern lean_object* l_Lean_protectedExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__27;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__10;
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_attrs___default;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__20;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
static lean_object* l_Lean_Elab_instToStringModifiers___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__19;
lean_object* l_Lean_Elab_elabDeclAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isProtected___boxed(lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__26;
static lean_object* l_Lean_Elab_instInhabitedModifiers___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedVisibility;
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_visibility___default;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__22;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object*);
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3;
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1;
static lean_object* l_Lean_Elab_expandDeclId___rarg___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__28;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__14;
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isUnsafe___default;
static lean_object* l_Lean_Elab_elabModifiers___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
static lean_object* l_Lean_Elab_expandDeclIdCore___closed__1;
static lean_object* l_Lean_Elab_mkDeclName___rarg___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object*);
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__15;
static lean_object* l_Lean_Elab_Modifiers_attrs___default___closed__1;
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5;
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__29;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToFormatModifiers___closed__16;
static lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringVisibility___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1___boxed(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instToStringVisibility___closed__1;
static lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a non-private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_11);
x_12 = l_Lean_Environment_contains(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___rarg(x_2, x_4, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
lean_inc(x_1);
lean_inc(x_3);
x_8 = l_Lean_mkPrivateName(x_3, x_1);
x_9 = l_Lean_Environment_contains(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___rarg(x_2, x_4, x_19);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_7);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_4);
lean_inc(x_1);
x_7 = l_Lean_Environment_contains(x_5, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___rarg(x_2, x_3, x_18);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___rarg(x_2, x_3, x_26);
x_28 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_27, x_6);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Visibility_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Visibility_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Visibility_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Visibility_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Visibility_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Visibility_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
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
static lean_object* _init_l_Lean_Elab_instToStringVisibility___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("regular");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringVisibility___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_instToStringVisibility___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_instToStringVisibility___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Elab_instToStringVisibility___closed__3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_instToStringVisibility(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_RecKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Visibility_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_RecKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_RecKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
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
static lean_object* _init_l_Lean_Elab_Modifiers_docString_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Modifiers_visibility___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Modifiers_isNoncomputable___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Modifiers_recKind___default() {
_start:
{
uint8_t x_1; 
x_1 = 2;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Modifiers_isUnsafe___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Modifiers_attrs___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Modifiers_attrs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedModifiers___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
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
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isPrivate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isProtected___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isProtected(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isPartial(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Modifiers_isNonrec(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_6);
lean_dec(x_1);
x_12 = lean_array_push(x_11, x_2);
x_13 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 1, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 2, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 3, x_10);
return x_13;
}
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@[");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("local ");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scoped ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_formatStxAux(x_13, x_14, x_15, x_12);
x_17 = l_Std_Format_defWidth;
x_18 = lean_format_pretty(x_16, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
switch (x_7) {
case 0:
{
lean_object* x_40; 
x_40 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1;
x_20 = x_40;
goto block_39;
}
case 1:
{
lean_object* x_41; 
x_41 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9;
x_20 = x_41;
goto block_39;
}
default: 
{
lean_object* x_42; 
x_42 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10;
x_20 = x_42;
goto block_39;
}
}
block_39:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5;
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
if (lean_is_scalar(x_6)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_6;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_1 = x_5;
x_2 = x_37;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsafe");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("partial");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nonrec");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noncomputable");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToStringVisibility___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToStringVisibility___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instToFormatModifiers___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/--");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-/");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatModifiers___closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_to_list(lean_box(0), x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1(x_8, x_9);
if (lean_obj_tag(x_2) == 0)
{
x_11 = x_9;
goto block_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_Elab_instToFormatModifiers___closed__27;
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_instToFormatModifiers___closed__29;
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
x_11 = x_58;
goto block_51;
}
block_51:
{
lean_object* x_12; 
switch (x_3) {
case 0:
{
x_12 = x_9;
goto block_48;
}
case 1:
{
lean_object* x_49; 
x_49 = l_Lean_Elab_instToFormatModifiers___closed__23;
x_12 = x_49;
goto block_48;
}
default: 
{
lean_object* x_50; 
x_50 = l_Lean_Elab_instToFormatModifiers___closed__25;
x_12 = x_50;
goto block_48;
}
}
block_48:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_appendTR___rarg(x_11, x_12);
if (x_4 == 0)
{
x_14 = x_9;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Elab_instToFormatModifiers___closed__21;
x_14 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_List_appendTR___rarg(x_13, x_14);
switch (x_5) {
case 0:
{
lean_object* x_44; 
x_44 = l_Lean_Elab_instToFormatModifiers___closed__15;
x_16 = x_44;
goto block_43;
}
case 1:
{
lean_object* x_45; 
x_45 = l_Lean_Elab_instToFormatModifiers___closed__18;
x_16 = x_45;
goto block_43;
}
default: 
{
x_16 = x_9;
goto block_43;
}
}
block_43:
{
lean_object* x_17; 
x_17 = l_List_appendTR___rarg(x_15, x_16);
if (x_6 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_18 = l_List_appendTR___rarg(x_17, x_9);
x_19 = l_List_appendTR___rarg(x_18, x_10);
x_20 = l_Lean_Elab_instToFormatModifiers___closed__3;
x_21 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_Elab_instToFormatModifiers___closed__7;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_instToFormatModifiers___closed__9;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_instToFormatModifiers___closed__6;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = 0;
x_29 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_30 = l_Lean_Elab_instToFormatModifiers___closed__12;
x_31 = l_List_appendTR___rarg(x_17, x_30);
x_32 = l_List_appendTR___rarg(x_31, x_10);
x_33 = l_Lean_Elab_instToFormatModifiers___closed__3;
x_34 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_32, x_33);
lean_dec(x_32);
x_35 = l_Lean_Elab_instToFormatModifiers___closed__7;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_instToFormatModifiers___closed__9;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_instToFormatModifiers___closed__6;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
x_42 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Format_defWidth;
x_3 = lean_format_pretty(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_to_list(lean_box(0), x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1(x_8, x_9);
if (lean_obj_tag(x_2) == 0)
{
x_11 = x_9;
goto block_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_Elab_instToFormatModifiers___closed__27;
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_instToFormatModifiers___closed__29;
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
x_11 = x_58;
goto block_51;
}
block_51:
{
lean_object* x_12; 
switch (x_3) {
case 0:
{
x_12 = x_9;
goto block_48;
}
case 1:
{
lean_object* x_49; 
x_49 = l_Lean_Elab_instToFormatModifiers___closed__23;
x_12 = x_49;
goto block_48;
}
default: 
{
lean_object* x_50; 
x_50 = l_Lean_Elab_instToFormatModifiers___closed__25;
x_12 = x_50;
goto block_48;
}
}
block_48:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_appendTR___rarg(x_11, x_12);
if (x_4 == 0)
{
x_14 = x_9;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Elab_instToFormatModifiers___closed__21;
x_14 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_List_appendTR___rarg(x_13, x_14);
switch (x_5) {
case 0:
{
lean_object* x_44; 
x_44 = l_Lean_Elab_instToFormatModifiers___closed__15;
x_16 = x_44;
goto block_43;
}
case 1:
{
lean_object* x_45; 
x_45 = l_Lean_Elab_instToFormatModifiers___closed__18;
x_16 = x_45;
goto block_43;
}
default: 
{
x_16 = x_9;
goto block_43;
}
}
block_43:
{
lean_object* x_17; 
x_17 = l_List_appendTR___rarg(x_15, x_16);
if (x_6 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_18 = l_List_appendTR___rarg(x_17, x_9);
x_19 = l_List_appendTR___rarg(x_18, x_10);
x_20 = l_Lean_Elab_instToFormatModifiers___closed__3;
x_21 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_Elab_instToFormatModifiers___closed__7;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_instToFormatModifiers___closed__9;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_instToFormatModifiers___closed__6;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = 0;
x_29 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_30 = l_Lean_Elab_instToFormatModifiers___closed__12;
x_31 = l_List_appendTR___rarg(x_17, x_30);
x_32 = l_List_appendTR___rarg(x_31, x_10);
x_33 = l_Lean_Elab_instToFormatModifiers___closed__3;
x_34 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_32, x_33);
lean_dec(x_32);
x_35 = l_Lean_Elab_instToFormatModifiers___closed__7;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_instToFormatModifiers___closed__9;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_instToFormatModifiers___closed__6;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
x_42 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
return x_42;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToStringModifiers___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToStringModifiers___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instToStringModifiers___closed__1;
x_2 = l_Lean_Elab_instToStringModifiers___closed__2;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instToStringModifiers() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instToStringModifiers___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected doc string");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getOptional_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_10, x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_string_utf8_byte_size(x_13);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_extract(x_13, x_19, x_18);
lean_dec(x_18);
lean_dec(x_13);
lean_ctor_set(x_4, 0, x_20);
x_21 = lean_apply_2(x_15, lean_box(0), x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_12);
x_23 = l_Lean_indentD(x_22);
x_24 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___rarg(x_1, x_2, x_10, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Syntax_getArg(x_29, x_30);
if (lean_obj_tag(x_31) == 2)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_string_utf8_byte_size(x_32);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_sub(x_35, x_36);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_string_utf8_extract(x_32, x_38, x_37);
lean_dec(x_37);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_apply_2(x_34, lean_box(0), x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_31);
x_43 = l_Lean_indentD(x_42);
x_44 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwErrorAt___rarg(x_1, x_2, x_29, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_expandOptDocComment_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_expandOptDocComment_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Syntax_isNone(x_2);
x_11 = l_Lean_Syntax_isNone(x_3);
if (x_10 == 0)
{
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 2, x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 3, x_12);
x_14 = lean_apply_2(x_9, lean_box(0), x_13);
return x_14;
}
else
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 2, x_6);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 3, x_16);
x_18 = lean_apply_2(x_9, lean_box(0), x_17);
return x_18;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = 1;
x_21 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 2, x_6);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 3, x_20);
x_22 = lean_apply_2(x_9, lean_box(0), x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 2, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 3, x_23);
x_25 = lean_apply_2(x_9, lean_box(0), x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(x_15);
x_17 = lean_box(x_5);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_17);
x_19 = l_Lean_Syntax_getOptional_x3f(x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_24, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = l_Lean_Elab_elabDeclAttrs___rarg(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
lean_dec(x_26);
x_29 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_28, x_18);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
x_2 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6;
x_2 = l_Lean_Elab_instToStringVisibility___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6;
x_2 = l_Lean_Elab_instToStringVisibility___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected visibility modifier");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(x_4);
lean_inc(x_8);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___rarg___lambda__2___boxed), 15, 14);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
lean_closure_set(x_17, 11, x_11);
lean_closure_set(x_17, 12, x_12);
lean_closure_set(x_17, 13, x_13);
x_18 = l_Lean_Syntax_getOptional_x3f(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_apply_2(x_21, lean_box(0), x_23);
x_25 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_24, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
lean_inc(x_26);
x_27 = l_Lean_Syntax_getKind(x_26);
x_28 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
x_29 = lean_name_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8;
x_31 = lean_name_eq(x_27, x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10;
x_34 = l_Lean_throwErrorAt___rarg(x_1, x_8, x_26, x_33);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_34, x_17);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_8);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_apply_2(x_38, lean_box(0), x_40);
x_42 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_41, x_17);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_8);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 2;
x_47 = lean_box(x_46);
x_48 = lean_apply_2(x_45, lean_box(0), x_47);
x_49 = lean_apply_4(x_43, lean_box(0), lean_box(0), x_48, x_17);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6;
x_2 = l_Lean_Elab_instToFormatModifiers___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_10, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_10, x_17);
x_19 = lean_unsigned_to_nat(4u);
x_20 = l_Lean_Syntax_getArg(x_10, x_19);
x_21 = lean_unsigned_to_nat(5u);
x_22 = l_Lean_Syntax_getArg(x_10, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
x_24 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (x_23 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = l_Lean_Syntax_getArg(x_22, x_11);
lean_dec(x_22);
x_78 = l_Lean_Syntax_getKind(x_77);
x_79 = l_Lean_Elab_elabModifiers___rarg___closed__1;
x_80 = lean_name_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = 1;
x_25 = x_81;
goto block_76;
}
else
{
uint8_t x_82; 
x_82 = 0;
x_25 = x_82;
goto block_76;
}
}
else
{
uint8_t x_83; 
lean_dec(x_22);
x_83 = 2;
x_25 = x_83;
goto block_76;
}
block_76:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(x_25);
lean_inc(x_4);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___rarg___lambda__3___boxed), 15, 14);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_18);
lean_closure_set(x_27, 2, x_20);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_14);
lean_closure_set(x_27, 5, x_2);
lean_closure_set(x_27, 6, x_3);
lean_closure_set(x_27, 7, x_4);
lean_closure_set(x_27, 8, x_5);
lean_closure_set(x_27, 9, x_6);
lean_closure_set(x_27, 10, x_7);
lean_closure_set(x_27, 11, x_8);
lean_closure_set(x_27, 12, x_9);
lean_closure_set(x_27, 13, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_apply_2(x_30, lean_box(0), x_31);
x_33 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_32, x_27);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = l_Lean_Syntax_getArg(x_35, x_13);
if (lean_obj_tag(x_36) == 2)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_string_utf8_byte_size(x_37);
x_42 = lean_nat_sub(x_41, x_15);
lean_dec(x_41);
x_43 = lean_string_utf8_extract(x_37, x_11, x_42);
lean_dec(x_42);
lean_dec(x_37);
lean_ctor_set(x_24, 0, x_43);
x_44 = lean_apply_2(x_40, lean_box(0), x_24);
x_45 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_44, x_27);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_24);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_36);
x_48 = l_Lean_indentD(x_47);
x_49 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwErrorAt___rarg(x_1, x_4, x_35, x_52);
x_54 = lean_apply_4(x_46, lean_box(0), lean_box(0), x_53, x_27);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_24, 0);
lean_inc(x_55);
lean_dec(x_24);
x_56 = l_Lean_Syntax_getArg(x_55, x_13);
if (lean_obj_tag(x_56) == 2)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_string_utf8_byte_size(x_57);
x_62 = lean_nat_sub(x_61, x_15);
lean_dec(x_61);
x_63 = lean_string_utf8_extract(x_57, x_11, x_62);
lean_dec(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_apply_2(x_60, lean_box(0), x_64);
x_66 = lean_apply_4(x_58, lean_box(0), lean_box(0), x_65, x_27);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_56);
x_69 = l_Lean_indentD(x_68);
x_70 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwErrorAt___rarg(x_1, x_4, x_55, x_73);
x_75 = lean_apply_4(x_67, lean_box(0), lean_box(0), x_74, x_27);
return x_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Elab_elabModifiers___rarg___lambda__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_15);
lean_dec(x_15);
x_18 = l_Lean_Elab_elabModifiers___rarg___lambda__2(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Elab_elabModifiers___rarg___lambda__3(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_elabModifiers___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_protectedExt;
lean_inc(x_1);
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_6, x_5, x_1);
x_8 = l_Lean_setEnv___rarg(x_2, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_mkPrivateName(x_6, x_1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Elab_checkNotAlreadyDeclared___rarg(x_2, x_3, x_4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
switch (x_4) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___rarg(x_1, x_2, x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___rarg(x_1, x_2, x_3, x_5);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__3___boxed), 5, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___lambda__4), 6, 5);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_14);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_applyVisibility___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_applyVisibility___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_applyVisibility___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_10);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_14);
return x_17;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1;
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid declaration name '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', structure '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has field '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_8 < x_7;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_14 = lean_array_uget(x_6, x_8);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_Lean_Name_append(x_4, x_14);
x_17 = lean_name_eq(x_16, x_3);
lean_dec(x_16);
x_18 = lean_box_usize(x_8);
x_19 = lean_box_usize(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_19);
if (x_17 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
lean_inc(x_22);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_25, 0, x_22);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_26, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_3);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_4);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_14);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_1);
x_41 = l_Lean_throwError___rarg(x_1, x_2, x_40);
x_42 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_42, 0, x_1);
x_43 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_41, x_42);
x_44 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_43, x_20);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_Lean_getStructureFieldsFlattened(x_6, x_1, x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_5);
lean_inc(x_2);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg(x_2, x_3, x_4, x_1, x_5, x_8, x_10, x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_1);
x_8 = l_Lean_isStructure(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__2), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_7);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_checkIfShadowingStructureField___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected declarations must be in a namespace");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_box(x_1);
if (lean_obj_tag(x_7) == 1)
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_name_mk_string(x_11, x_8);
x_13 = l_Lean_Name_append(x_12, x_3);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_10, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2;
x_17 = l_Lean_throwError___rarg(x_2, x_5, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Lean_Elab_applyVisibility___rarg(x_2, x_3, x_4, x_10, x_5);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_4);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_8 = l_Lean_Name_append(x_1, x_2);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_checkIfShadowingStructureField___rarg(x_3, x_4, x_5, x_8);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___rarg___lambda__2___boxed), 9, 8);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_2);
lean_closure_set(x_11, 6, x_1);
lean_closure_set(x_11, 7, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("atomic identifier expected '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_6);
x_7 = l_Lean_extractMacroScopes(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_3);
lean_closure_set(x_9, 5, x_5);
x_10 = l_Lean_Name_isAtomic(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Elab_isFreshInstanceName(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_6);
x_14 = l_Lean_Elab_mkDeclName___rarg___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___rarg(x_1, x_3, x_17);
x_19 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_18, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_24, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
x_31 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_30, x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Elab_mkDeclName___rarg___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_mkDeclName___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_mkDeclName___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclIdCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_10 = l_Lean_Elab_expandDeclIdCore___closed__1;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = x_1 + x_8;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg(x_2, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_3(x_6, lean_box(0), x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_5 == x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lean_Syntax_getId(x_10);
x_12 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_11, x_7);
x_13 = lean_box_usize(x_5);
x_14 = lean_box_usize(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_14);
if (x_12 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_7);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_19, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg(x_1, x_2, x_11);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_24, 0, x_10);
lean_closure_set(x_24, 1, x_21);
lean_closure_set(x_24, 2, x_22);
x_25 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_24);
x_26 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_25, x_15);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_2(x_28, lean_box(0), x_7);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_2);
x_10 = l_Lean_addDocString_x27___rarg(x_2, x_3, x_7, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_4);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Elab_mkDeclName___rarg(x_1, x_3, x_2, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_inc(x_9);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___rarg___lambda__2), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_8);
lean_closure_set(x_15, 4, x_9);
x_16 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_expandDeclId___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Elab_expandDeclIdCore(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___rarg___lambda__3), 8, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_9);
lean_closure_set(x_11, 6, x_6);
x_12 = l_Lean_Syntax_isNone(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
if (x_18 == 0)
{
lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_15);
x_37 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_20 = x_37;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_16, x_16);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_16);
lean_dec(x_15);
x_39 = l_Lean_Elab_Modifiers_attrs___default___closed__1;
x_20 = x_39;
goto block_36;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_42 = l_Lean_Elab_expandDeclId___rarg___closed__1;
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_15, x_40, x_41, x_42);
lean_dec(x_15);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_20 = x_44;
goto block_36;
}
}
block_36:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_17, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_2(x_24, lean_box(0), x_5);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_25, x_11);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_21, x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_apply_2(x_29, lean_box(0), x_5);
x_31 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_30, x_11);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_21);
lean_dec(x_21);
lean_inc(x_19);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg(x_1, x_3, x_19, x_20, x_32, x_33, x_5);
x_35 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_34, x_11);
return x_35;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_3);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_apply_2(x_47, lean_box(0), x_5);
x_49 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_48, x_11);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_expandDeclId___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_expandDeclId___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_expandDeclId___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Modifiers(lean_object*);
lean_object* initialize_Lean_DocString(lean_object*);
lean_object* initialize_Lean_Elab_Attributes(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclModifiers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Modifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__4);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3);
l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4 = _init_l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__4);
l_Lean_Elab_Visibility_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_Visibility_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Visibility_noConfusion___rarg___closed__1);
l_Lean_Elab_instInhabitedVisibility = _init_l_Lean_Elab_instInhabitedVisibility();
l_Lean_Elab_instToStringVisibility___closed__1 = _init_l_Lean_Elab_instToStringVisibility___closed__1();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___closed__1);
l_Lean_Elab_instToStringVisibility___closed__2 = _init_l_Lean_Elab_instToStringVisibility___closed__2();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___closed__2);
l_Lean_Elab_instToStringVisibility___closed__3 = _init_l_Lean_Elab_instToStringVisibility___closed__3();
lean_mark_persistent(l_Lean_Elab_instToStringVisibility___closed__3);
l_Lean_Elab_instInhabitedRecKind = _init_l_Lean_Elab_instInhabitedRecKind();
l_Lean_Elab_Modifiers_docString_x3f___default = _init_l_Lean_Elab_Modifiers_docString_x3f___default();
lean_mark_persistent(l_Lean_Elab_Modifiers_docString_x3f___default);
l_Lean_Elab_Modifiers_visibility___default = _init_l_Lean_Elab_Modifiers_visibility___default();
l_Lean_Elab_Modifiers_isNoncomputable___default = _init_l_Lean_Elab_Modifiers_isNoncomputable___default();
l_Lean_Elab_Modifiers_recKind___default = _init_l_Lean_Elab_Modifiers_recKind___default();
l_Lean_Elab_Modifiers_isUnsafe___default = _init_l_Lean_Elab_Modifiers_isUnsafe___default();
l_Lean_Elab_Modifiers_attrs___default___closed__1 = _init_l_Lean_Elab_Modifiers_attrs___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Modifiers_attrs___default___closed__1);
l_Lean_Elab_Modifiers_attrs___default = _init_l_Lean_Elab_Modifiers_attrs___default();
lean_mark_persistent(l_Lean_Elab_Modifiers_attrs___default);
l_Lean_Elab_instInhabitedModifiers___closed__1 = _init_l_Lean_Elab_instInhabitedModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedModifiers___closed__1);
l_Lean_Elab_instInhabitedModifiers = _init_l_Lean_Elab_instInhabitedModifiers();
lean_mark_persistent(l_Lean_Elab_instInhabitedModifiers);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__1);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__2);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__3);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__4);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__5);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__6);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__7);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__8);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__9);
l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10 = _init_l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_instToFormatModifiers___spec__1___closed__10);
l_Lean_Elab_instToFormatModifiers___closed__1 = _init_l_Lean_Elab_instToFormatModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__1);
l_Lean_Elab_instToFormatModifiers___closed__2 = _init_l_Lean_Elab_instToFormatModifiers___closed__2();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__2);
l_Lean_Elab_instToFormatModifiers___closed__3 = _init_l_Lean_Elab_instToFormatModifiers___closed__3();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__3);
l_Lean_Elab_instToFormatModifiers___closed__4 = _init_l_Lean_Elab_instToFormatModifiers___closed__4();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__4);
l_Lean_Elab_instToFormatModifiers___closed__5 = _init_l_Lean_Elab_instToFormatModifiers___closed__5();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__5);
l_Lean_Elab_instToFormatModifiers___closed__6 = _init_l_Lean_Elab_instToFormatModifiers___closed__6();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__6);
l_Lean_Elab_instToFormatModifiers___closed__7 = _init_l_Lean_Elab_instToFormatModifiers___closed__7();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__7);
l_Lean_Elab_instToFormatModifiers___closed__8 = _init_l_Lean_Elab_instToFormatModifiers___closed__8();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__8);
l_Lean_Elab_instToFormatModifiers___closed__9 = _init_l_Lean_Elab_instToFormatModifiers___closed__9();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__9);
l_Lean_Elab_instToFormatModifiers___closed__10 = _init_l_Lean_Elab_instToFormatModifiers___closed__10();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__10);
l_Lean_Elab_instToFormatModifiers___closed__11 = _init_l_Lean_Elab_instToFormatModifiers___closed__11();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__11);
l_Lean_Elab_instToFormatModifiers___closed__12 = _init_l_Lean_Elab_instToFormatModifiers___closed__12();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__12);
l_Lean_Elab_instToFormatModifiers___closed__13 = _init_l_Lean_Elab_instToFormatModifiers___closed__13();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__13);
l_Lean_Elab_instToFormatModifiers___closed__14 = _init_l_Lean_Elab_instToFormatModifiers___closed__14();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__14);
l_Lean_Elab_instToFormatModifiers___closed__15 = _init_l_Lean_Elab_instToFormatModifiers___closed__15();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__15);
l_Lean_Elab_instToFormatModifiers___closed__16 = _init_l_Lean_Elab_instToFormatModifiers___closed__16();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__16);
l_Lean_Elab_instToFormatModifiers___closed__17 = _init_l_Lean_Elab_instToFormatModifiers___closed__17();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__17);
l_Lean_Elab_instToFormatModifiers___closed__18 = _init_l_Lean_Elab_instToFormatModifiers___closed__18();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__18);
l_Lean_Elab_instToFormatModifiers___closed__19 = _init_l_Lean_Elab_instToFormatModifiers___closed__19();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__19);
l_Lean_Elab_instToFormatModifiers___closed__20 = _init_l_Lean_Elab_instToFormatModifiers___closed__20();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__20);
l_Lean_Elab_instToFormatModifiers___closed__21 = _init_l_Lean_Elab_instToFormatModifiers___closed__21();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__21);
l_Lean_Elab_instToFormatModifiers___closed__22 = _init_l_Lean_Elab_instToFormatModifiers___closed__22();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__22);
l_Lean_Elab_instToFormatModifiers___closed__23 = _init_l_Lean_Elab_instToFormatModifiers___closed__23();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__23);
l_Lean_Elab_instToFormatModifiers___closed__24 = _init_l_Lean_Elab_instToFormatModifiers___closed__24();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__24);
l_Lean_Elab_instToFormatModifiers___closed__25 = _init_l_Lean_Elab_instToFormatModifiers___closed__25();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__25);
l_Lean_Elab_instToFormatModifiers___closed__26 = _init_l_Lean_Elab_instToFormatModifiers___closed__26();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__26);
l_Lean_Elab_instToFormatModifiers___closed__27 = _init_l_Lean_Elab_instToFormatModifiers___closed__27();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__27);
l_Lean_Elab_instToFormatModifiers___closed__28 = _init_l_Lean_Elab_instToFormatModifiers___closed__28();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__28);
l_Lean_Elab_instToFormatModifiers___closed__29 = _init_l_Lean_Elab_instToFormatModifiers___closed__29();
lean_mark_persistent(l_Lean_Elab_instToFormatModifiers___closed__29);
l_Lean_Elab_instToStringModifiers___closed__1 = _init_l_Lean_Elab_instToStringModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers___closed__1);
l_Lean_Elab_instToStringModifiers___closed__2 = _init_l_Lean_Elab_instToStringModifiers___closed__2();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers___closed__2);
l_Lean_Elab_instToStringModifiers___closed__3 = _init_l_Lean_Elab_instToStringModifiers___closed__3();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers___closed__3);
l_Lean_Elab_instToStringModifiers = _init_l_Lean_Elab_instToStringModifiers();
lean_mark_persistent(l_Lean_Elab_instToStringModifiers);
l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1 = _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__1);
l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2 = _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__2);
l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3 = _init_l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_expandOptDocComment_x3f___rarg___closed__3);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__5);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__6);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__8);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__9);
l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10 = _init_l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__10);
l_Lean_Elab_elabModifiers___rarg___closed__1 = _init_l_Lean_Elab_elabModifiers___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_checkIfShadowingStructureField___spec__1___rarg___closed__6);
l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__1);
l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__2);
l_Lean_Elab_mkDeclName___rarg___closed__1 = _init_l_Lean_Elab_mkDeclName___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___rarg___closed__1);
l_Lean_Elab_mkDeclName___rarg___closed__2 = _init_l_Lean_Elab_mkDeclName___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___rarg___closed__2);
l_Lean_Elab_expandDeclIdCore___closed__1 = _init_l_Lean_Elab_expandDeclIdCore___closed__1();
lean_mark_persistent(l_Lean_Elab_expandDeclIdCore___closed__1);
l_Lean_Elab_expandDeclId___rarg___closed__1 = _init_l_Lean_Elab_expandDeclId___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_expandDeclId___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
