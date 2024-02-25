// Lean compiler output
// Module: Lean.Elab.GuardMsgs
// Imports: Init Lean.Server.CodeActions.Attr
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5;
lean_object* l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5;
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__7(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6;
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10;
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3;
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2;
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4;
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__6(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
uint32_t l_String_back(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__1(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5;
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(uint8_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1;
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1;
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1;
x_5 = l_String_isEmpty(x_1);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = l_String_back(x_1);
x_7 = 10;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
x_10 = lean_string_append(x_1, x_9);
x_11 = lean_box(0);
x_12 = lean_apply_3(x_4, x_10, x_11, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_apply_3(x_4, x_1, x_13, x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
x_16 = lean_string_append(x_1, x_15);
x_17 = lean_box(0);
x_18 = lean_apply_3(x_4, x_16, x_17, x_3);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info:", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning:", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error:", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1;
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
switch (x_6) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2;
x_8 = lean_string_append(x_7, x_2);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_5, x_8, x_9, x_4);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3;
x_12 = lean_string_append(x_11, x_2);
x_13 = lean_box(0);
x_14 = lean_apply_3(x_5, x_12, x_13, x_4);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4;
x_16 = lean_string_append(x_15, x_2);
x_17 = lean_box(0);
x_18 = lean_apply_3(x_5, x_16, x_17, x_4);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_3);
x_5 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
x_6 = l_String_isPrefixOf(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1;
x_8 = lean_string_append(x_7, x_2);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3(x_1, x_8, x_9, x_4);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3(x_1, x_2, x_11, x_4);
lean_dec(x_2);
return x_12;
}
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":\n", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = l_Lean_MessageData_toString(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2;
x_11 = lean_string_append(x_7, x_10);
x_12 = lean_string_append(x_11, x_5);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4(x_1, x_12, x_13, x_6);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4(x_1, x_5, x_15, x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2(x_2, x_3, x_4, x_8);
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
x_21 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__18(x_2, x_3, x_4, x_8);
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
x_21 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__18(x_2, x_20, x_4, x_8);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 2;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 2;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 1;
x_8 = lean_box(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 1;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 1;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 1;
x_8 = lean_box(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 0;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__7(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = 0;
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_2);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 1;
x_8 = lean_box(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("token", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning", 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("all", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid #guard_msgs specification element", 41);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5;
lean_inc(x_9);
x_13 = l_Lean_Syntax_isOfKind(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7;
lean_inc(x_9);
x_15 = l_Lean_Syntax_isOfKind(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9;
x_17 = l_Lean_Syntax_isOfKind(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11;
x_19 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(x_1, x_18, x_5, x_6, x_7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
else
{
lean_dec(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__2), 2, 1);
lean_closure_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_30 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__3), 2, 1);
lean_closure_set(x_30, 0, x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__4), 2, 1);
lean_closure_set(x_33, 0, x_2);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_36 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__5), 2, 1);
lean_closure_set(x_36, 0, x_2);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__6), 2, 1);
lean_closure_set(x_39, 0, x_2);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_42 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__7), 2, 1);
lean_closure_set(x_42, 0, x_2);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardMsgsSpecElt", 16);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; uint8_t x_19; 
x_10 = lean_array_uget(x_1, x_3);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3;
lean_inc(x_10);
x_19 = l_Lean_Syntax_isOfKind(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11;
x_21 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(x_10, x_20, x_5, x_6, x_7);
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_10, x_26);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(1u);
lean_inc(x_27);
x_30 = l_Lean_Syntax_matchesNull(x_27, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_4);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11;
x_32 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(x_10, x_31, x_5, x_6, x_7);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Lean_Syntax_getArg(x_27, x_26);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
lean_inc(x_5);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8(x_10, x_4, x_39, x_38, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_11 = x_41;
x_12 = x_42;
goto block_17;
}
else
{
uint8_t x_43; 
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
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
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = lean_box(0);
lean_inc(x_5);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8(x_10, x_4, x_48, x_47, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_11 = x_50;
x_12 = x_51;
goto block_17;
}
else
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
x_7 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3;
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
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardMsgsSpec", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid #guard_msgs specification", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3;
lean_inc(x_7);
x_9 = l_Lean_Syntax_isOfKind(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5;
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__1(x_7, x_10, x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_7, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_14);
x_39 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6;
x_18 = x_39;
goto block_38;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_15, x_15);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_15);
lean_dec(x_14);
x_41 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6;
x_18 = x_41;
goto block_38;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_44 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7;
x_45 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_14, x_42, x_43, x_44);
lean_dec(x_14);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_18 = x_46;
goto block_38;
}
}
block_38:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8;
x_20 = l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5;
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__1(x_7, x_21, x_2, x_3, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Array_reverse___rarg(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9;
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6(x_24, x_26, x_27, x_28, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_24);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___elambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GuardMsgs", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GuardMsgFailure", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1;
x_3 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2;
x_4 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3;
x_5 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_8);
x_13 = lean_apply_1(x_1, x_8);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_push___rarg(x_11, x_8);
lean_ctor_set(x_3, 0, x_15);
x_2 = x_9;
goto _start;
}
case 1:
{
lean_dec(x_8);
x_2 = x_9;
goto _start;
}
default: 
{
lean_object* x_18; 
x_18 = l_Lean_PersistentArray_push___rarg(x_12, x_8);
lean_ctor_set(x_3, 1, x_18);
x_2 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_8);
x_22 = lean_apply_1(x_1, x_8);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
switch (x_23) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_PersistentArray_push___rarg(x_20, x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_2 = x_9;
x_3 = x_25;
goto _start;
}
case 1:
{
lean_object* x_27; 
lean_dec(x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
x_2 = x_9;
x_3 = x_27;
goto _start;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_PersistentArray_push___rarg(x_21, x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
x_2 = x_9;
x_3 = x_30;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___rarg(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(x_9, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_12);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_4 = x_13;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_5 = _tmp_4;
}
goto _start;
}
else
{
uint8_t x_15; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_ctor_get(x_3, 6);
x_25 = lean_io_error_to_string(x_22);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_32 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(x_30, x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
x_1 = x_31;
x_2 = x_35;
x_5 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
lean_dec(x_2);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_3, 6);
x_41 = lean_io_error_to_string(x_37);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_39;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6(x_2, x_3, x_4, x_8);
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
x_21 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected doc string", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_7, x_11, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_MessageData_ofSyntax(x_6);
x_15 = l_Lean_indentD(x_14);
x_16 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__5(x_1, x_19, x_2, x_3, x_4);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageLog_empty;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("---\n", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("❌ Docstring on `#guard_msgs` does not match generated message:\n\n", 66);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_269; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_269 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_box(0);
x_13 = x_270;
goto block_268;
}
else
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
x_13 = x_269;
goto block_268;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_13 = x_273;
goto block_268;
}
}
block_268:
{
lean_object* x_14; lean_object* x_15; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_249; 
x_249 = lean_box(0);
x_14 = x_249;
x_15 = x_6;
goto block_248;
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_3);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_4);
x_252 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4(x_251, x_4, x_5, x_6);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_ctor_set(x_3, 0, x_253);
x_14 = x_3;
x_15 = x_254;
goto block_248;
}
else
{
uint8_t x_255; 
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_255 = !lean_is_exclusive(x_252);
if (x_255 == 0)
{
return x_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_252, 0);
x_257 = lean_ctor_get(x_252, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_252);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_3, 0);
lean_inc(x_259);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_4);
x_260 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4(x_259, x_4, x_5, x_6);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_261);
x_14 = x_263;
x_15 = x_262;
goto block_248;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_264 = lean_ctor_get(x_260, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_266 = x_260;
} else {
 lean_dec_ref(x_260);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
block_248:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(x_13, x_4, x_5, x_15);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_246; 
x_246 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1;
x_17 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_14, 0);
lean_inc(x_247);
lean_dec(x_14);
x_17 = x_247;
goto block_245;
}
block_245:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_String_trim(x_17);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_5, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3;
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_5, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Elab_Command_elabCommandTopLevel(x_12, x_4, x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_5, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_34);
x_35 = l_Lean_MessageLog_toList(x_34);
x_36 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4;
x_37 = l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2(x_18, x_35, x_36, x_4, x_5, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_MessageLog_toList(x_40);
x_43 = lean_box(0);
x_44 = l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3(x_42, x_43, x_4, x_5, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5;
x_48 = l_String_intercalate(x_47, x_45);
x_49 = l_String_trim(x_48);
lean_dec(x_48);
x_50 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
x_51 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1;
x_52 = l_String_replace(x_20, x_50, x_51);
lean_dec(x_20);
x_53 = l_String_replace(x_49, x_50, x_51);
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_41);
x_55 = lean_st_ref_take(x_5, x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
x_60 = l_Lean_PersistentArray_append___rarg(x_25, x_34);
lean_ctor_set(x_56, 1, x_60);
x_61 = lean_st_ref_set(x_5, x_56, x_57);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_stringToMessageData(x_49);
x_64 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = 2;
x_69 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_8, x_67, x_68, x_4, x_5, x_62);
lean_dec(x_8);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Elab_Command_getRef(x_4, x_5, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_49);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(x_77, x_4, x_5, x_73);
lean_dec(x_5);
lean_dec(x_4);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_79 = lean_ctor_get(x_56, 0);
x_80 = lean_ctor_get(x_56, 2);
x_81 = lean_ctor_get(x_56, 3);
x_82 = lean_ctor_get(x_56, 4);
x_83 = lean_ctor_get(x_56, 5);
x_84 = lean_ctor_get(x_56, 6);
x_85 = lean_ctor_get(x_56, 7);
x_86 = lean_ctor_get(x_56, 8);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_56);
x_87 = l_Lean_PersistentArray_append___rarg(x_25, x_34);
x_88 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_80);
lean_ctor_set(x_88, 3, x_81);
lean_ctor_set(x_88, 4, x_82);
lean_ctor_set(x_88, 5, x_83);
lean_ctor_set(x_88, 6, x_84);
lean_ctor_set(x_88, 7, x_85);
lean_ctor_set(x_88, 8, x_86);
x_89 = lean_st_ref_set(x_5, x_88, x_57);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_stringToMessageData(x_49);
x_92 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = 2;
x_97 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_8, x_95, x_96, x_4, x_5, x_90);
lean_dec(x_8);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_Elab_Command_getRef(x_4, x_5, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure;
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_49);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(x_105, x_4, x_5, x_101);
lean_dec(x_5);
lean_dec(x_4);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_4);
x_107 = lean_st_ref_take(x_5, x_46);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_108, 1);
lean_dec(x_111);
x_112 = l_Lean_PersistentArray_append___rarg(x_25, x_41);
lean_ctor_set(x_108, 1, x_112);
x_113 = lean_st_ref_set(x_5, x_108, x_109);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
x_116 = lean_box(0);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_108, 0);
x_121 = lean_ctor_get(x_108, 2);
x_122 = lean_ctor_get(x_108, 3);
x_123 = lean_ctor_get(x_108, 4);
x_124 = lean_ctor_get(x_108, 5);
x_125 = lean_ctor_get(x_108, 6);
x_126 = lean_ctor_get(x_108, 7);
x_127 = lean_ctor_get(x_108, 8);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_108);
x_128 = l_Lean_PersistentArray_append___rarg(x_25, x_41);
x_129 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_121);
lean_ctor_set(x_129, 3, x_122);
lean_ctor_set(x_129, 4, x_123);
lean_ctor_set(x_129, 5, x_124);
lean_ctor_set(x_129, 6, x_125);
lean_ctor_set(x_129, 7, x_126);
lean_ctor_set(x_129, 8, x_127);
x_130 = lean_st_ref_set(x_5, x_129, x_109);
lean_dec(x_5);
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
x_133 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_135 = !lean_is_exclusive(x_44);
if (x_135 == 0)
{
return x_44;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_44, 0);
x_137 = lean_ctor_get(x_44, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_44);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_139 = !lean_is_exclusive(x_29);
if (x_139 == 0)
{
return x_29;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_29, 0);
x_141 = lean_ctor_get(x_29, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_29);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_143 = lean_ctor_get(x_22, 0);
x_144 = lean_ctor_get(x_22, 1);
x_145 = lean_ctor_get(x_22, 2);
x_146 = lean_ctor_get(x_22, 3);
x_147 = lean_ctor_get(x_22, 4);
x_148 = lean_ctor_get(x_22, 5);
x_149 = lean_ctor_get(x_22, 6);
x_150 = lean_ctor_get(x_22, 7);
x_151 = lean_ctor_get(x_22, 8);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_22);
x_152 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3;
x_153 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_145);
lean_ctor_set(x_153, 3, x_146);
lean_ctor_set(x_153, 4, x_147);
lean_ctor_set(x_153, 5, x_148);
lean_ctor_set(x_153, 6, x_149);
lean_ctor_set(x_153, 7, x_150);
lean_ctor_set(x_153, 8, x_151);
x_154 = lean_st_ref_set(x_5, x_153, x_23);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
lean_inc(x_5);
lean_inc(x_4);
x_156 = l_Lean_Elab_Command_elabCommandTopLevel(x_12, x_4, x_5, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_st_ref_get(x_5, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_161);
x_162 = l_Lean_MessageLog_toList(x_161);
x_163 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4;
x_164 = l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2(x_18, x_162, x_163, x_4, x_5, x_160);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l_Lean_MessageLog_toList(x_167);
x_170 = lean_box(0);
x_171 = l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3(x_169, x_170, x_4, x_5, x_166);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5;
x_175 = l_String_intercalate(x_174, x_172);
x_176 = l_String_trim(x_175);
lean_dec(x_175);
x_177 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2;
x_178 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1;
x_179 = l_String_replace(x_20, x_177, x_178);
lean_dec(x_20);
x_180 = l_String_replace(x_176, x_177, x_178);
x_181 = lean_string_dec_eq(x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_168);
x_182 = lean_st_ref_take(x_5, x_173);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 5);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 6);
lean_inc(x_190);
x_191 = lean_ctor_get(x_183, 7);
lean_inc(x_191);
x_192 = lean_ctor_get(x_183, 8);
lean_inc(x_192);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 lean_ctor_release(x_183, 6);
 lean_ctor_release(x_183, 7);
 lean_ctor_release(x_183, 8);
 x_193 = x_183;
} else {
 lean_dec_ref(x_183);
 x_193 = lean_box(0);
}
x_194 = l_Lean_PersistentArray_append___rarg(x_144, x_161);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 9, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_186);
lean_ctor_set(x_195, 3, x_187);
lean_ctor_set(x_195, 4, x_188);
lean_ctor_set(x_195, 5, x_189);
lean_ctor_set(x_195, 6, x_190);
lean_ctor_set(x_195, 7, x_191);
lean_ctor_set(x_195, 8, x_192);
x_196 = lean_st_ref_set(x_5, x_195, x_184);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = l_Lean_stringToMessageData(x_176);
x_199 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3;
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = 2;
x_204 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_8, x_202, x_203, x_4, x_5, x_197);
lean_dec(x_8);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l_Lean_Elab_Command_getRef(x_4, x_5, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_176);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(x_212, x_4, x_5, x_208);
lean_dec(x_5);
lean_dec(x_4);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_176);
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_4);
x_214 = lean_st_ref_take(x_5, x_173);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_215, 4);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 5);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 6);
lean_inc(x_222);
x_223 = lean_ctor_get(x_215, 7);
lean_inc(x_223);
x_224 = lean_ctor_get(x_215, 8);
lean_inc(x_224);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 lean_ctor_release(x_215, 5);
 lean_ctor_release(x_215, 6);
 lean_ctor_release(x_215, 7);
 lean_ctor_release(x_215, 8);
 x_225 = x_215;
} else {
 lean_dec_ref(x_215);
 x_225 = lean_box(0);
}
x_226 = l_Lean_PersistentArray_append___rarg(x_144, x_168);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 9, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_218);
lean_ctor_set(x_227, 3, x_219);
lean_ctor_set(x_227, 4, x_220);
lean_ctor_set(x_227, 5, x_221);
lean_ctor_set(x_227, 6, x_222);
lean_ctor_set(x_227, 7, x_223);
lean_ctor_set(x_227, 8, x_224);
x_228 = lean_st_ref_set(x_5, x_227, x_216);
lean_dec(x_5);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = lean_box(0);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_229);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_168);
lean_dec(x_161);
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_233 = lean_ctor_get(x_171, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_171, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_235 = x_171;
} else {
 lean_dec_ref(x_171);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_237 = lean_ctor_get(x_156, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_156, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_239 = x_156;
} else {
 lean_dec_ref(x_156);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_241 = !lean_is_exclusive(x_16);
if (x_241 == 0)
{
return x_16;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_16, 0);
x_243 = lean_ctor_get(x_16, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_16);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardMsgsCmd", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
x_3 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4;
x_4 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = l_Lean_Syntax_matchesNull(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_15 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1(x_1, x_19, x_18, x_2, x_3, x_4);
lean_dec(x_1);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1(x_1, x_22, x_21, x_2, x_3, x_4);
lean_dec(x_1);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabGuardMsgs", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1;
x_3 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2;
x_4 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
x_3 = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(99u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5;
x_4 = lean_unsigned_to_nat(59u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_Attr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_GuardMsgs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__1);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__2___closed__2);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__1);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__2);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__3);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__3___closed__4);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___lambda__4___closed__1);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__1);
l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2 = _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2();
lean_mark_persistent(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos___closed__2);
l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___lambda__8___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___spec__6___closed__3);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8);
l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9 = _init_l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__9);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1 = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__1);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2 = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__2);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3 = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__3);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4 = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__4);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5 = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100____closed__5);
l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_ = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1100_);
l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure = _init_l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__1___rarg___closed__2);
l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1 = _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__1);
l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2 = _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__2);
l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3 = _init_l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___spec__4___closed__3);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__1);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__2);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__3);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__4);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__5);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__6);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___lambda__1___closed__7);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6 = _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
