// Lean compiler output
// Module: Lean.Message
// Imports: Init Lean.Data.Position Lean.Data.OpenDecl Lean.MetavarContext Lean.Environment Lean.Util.PPExt Lean.Util.Sorry
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
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14;
LEAN_EXPORT lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppendMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___default;
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object*);
static lean_object* l_Lean_MessageData_instCoeSyntaxMessageData___closed__1;
static lean_object* l_Lean_mkErrorStringWithPos___closed__4;
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Message_severity___default;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Message_toString___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_KernelException_toMessageData___closed__4;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5;
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__50;
static lean_object* l_Lean_KernelException_toMessageData___closed__36;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__6;
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeExprMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__19;
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static size_t l_Lean_instInhabitedMessageLog___closed__3;
static lean_object* l_Lean_MessageData_ofList___closed__4;
LEAN_EXPORT uint8_t l_Lean_Message_keepFullRange___default;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__3;
static lean_object* l_Lean_MessageLog_msgs___default___closed__3;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageData(lean_object*);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(size_t, size_t, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExprMessageData(lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessage;
static lean_object* l_Lean_KernelException_toMessageData___closed__8;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_KernelException_toMessageData___closed__37;
static lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object*);
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
static lean_object* l_Lean_MessageLog_msgs___default___closed__2;
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__16;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__5;
LEAN_EXPORT lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarIdMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isEmpty___boxed(lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__7;
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__25;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__2;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8;
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeStringMessageData;
LEAN_EXPORT uint8_t l_Lean_MessageLog_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSyntax;
static lean_object* l_Lean_termM_x21_____closed__12;
static lean_object* l_Lean_KernelException_toMessageData___closed__34;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_instBEqMessageSeverity___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__32;
static lean_object* l_Lean_MessageData_formatAux___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExprMessageData(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PPFormat_hasSyntheticSorry___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_instInhabitedMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_instAddMessageContext___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__44;
static lean_object* l_Lean_mkErrorStringWithPos___closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__7;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataExpr;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__30;
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__8;
static lean_object* l_Lean_MessageData_formatAux___closed__4;
LEAN_EXPORT lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__35;
static lean_object* l_Lean_KernelException_toMessageData___closed__38;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageData___rarg(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Message_toString___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataFormat(lean_object*);
static lean_object* l_Lean_MessageData_instCoeNameMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData;
static lean_object* l_Lean_KernelException_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__5;
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__3;
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__6;
static lean_object* l_Lean_KernelException_toMessageData___closed__33;
static lean_object* l_Lean_KernelException_toMessageData___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__24;
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__2;
LEAN_EXPORT lean_object* l_Lean_PPFormat_hasSyntheticSorry___default___boxed(lean_object*);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11;
static lean_object* l_Lean_KernelException_toMessageData___closed__45;
static lean_object* l_Lean_KernelException_toMessageData___closed__46;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExprMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_MessageData_instCoeListMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog;
static lean_object* l_Lean_KernelException_toMessageData___closed__9;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataString;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__4;
static lean_object* l_Lean_KernelException_toMessageData___closed__29;
LEAN_EXPORT lean_object* l_Lean_instAddMessageContext(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__3;
static lean_object* l_Lean_MessageData_ofList___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__2;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(lean_object*);
static lean_object* l_Lean_MessageLog_instAppendMessageLog___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__12;
static lean_object* l_Lean_termM_x21_____closed__4;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Message_toString___lambda__3___closed__1;
LEAN_EXPORT uint8_t l_Lean_MessageData_isEmpty(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__11;
LEAN_EXPORT lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___boxed(lean_object*);
static lean_object* l_Lean_MessageLog_msgs___default___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(lean_object*, size_t, size_t);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15;
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__3;
uint8_t l_Std_Format_isEmpty(lean_object*);
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__2;
LEAN_EXPORT lean_object* l_String_split___at_Lean_stringToMessageData___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lambda__2(lean_object*);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9;
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__4;
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeSyntaxMessageData;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__40;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataLevel;
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeLevelMessageData;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__6;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__3;
static lean_object* l_Lean_KernelException_toMessageData___closed__7;
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__1;
static lean_object* l_Lean_termM_x21_____closed__8;
static lean_object* l_Lean_KernelException_toMessageData___closed__41;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataMVarId(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__43;
static lean_object* l_Lean_toMessageList___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__42;
static lean_object* l_Lean_MessageData_formatAux___closed__9;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__5;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__4;
static lean_object* l_Lean_MessageSeverity_noConfusion___rarg___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__15;
static lean_object* l_Lean_MessageData_formatAux___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_instInhabitedMessage___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__48;
LEAN_EXPORT lean_object* l_Lean_MessageLog_instAppendMessageLog;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_endPos___default;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_termM_x21__;
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object*);
uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__28;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeExprMessageData;
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__39;
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__2;
lean_object* l_Lean_Level_format(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__22;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__31;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__5;
static lean_object* l_Lean_KernelException_toMessageData___closed__18;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedMessageLog___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object*);
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__13;
static lean_object* l_Lean_termM_x21_____closed__9;
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object*);
static lean_object* l_Lean_Message_toString___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_toMessageList___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__5;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataMessageData;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___lambda__1(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_KernelException_mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_paren___closed__1;
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object*);
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__1;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
static lean_object* l_Lean_MessageData_ofList___closed__1;
static lean_object* l_Lean_instInhabitedMessageLog___closed__4;
static lean_object* l_Lean_KernelException_toMessageData___closed__26;
LEAN_EXPORT lean_object* l_Lean_Message_caption___default;
static lean_object* l_Lean_termM_x21_____closed__15;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l_Lean_mkErrorStringWithPos___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__47;
lean_object* l_Lean_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_format___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListMessageData;
static lean_object* l_Lean_KernelException_toMessageData___closed__49;
static lean_object* l_Lean_MessageData_instCoeLevelMessageData___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_stringToMessageData___spec__3___at_Lean_stringToMessageData___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__14;
static lean_object* l_Lean_termM_x21_____closed__10;
static lean_object* l_Lean_KernelException_toMessageData___closed__5;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_MessageData_ofList___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__8;
static lean_object* l_Lean_KernelException_toMessageData___closed__11;
static lean_object* l_Lean_KernelException_toMessageData___closed__20;
static lean_object* l_Lean_KernelException_toMessageData___closed__17;
static lean_object* l_Lean_instToMessageDataString___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_stringToMessageData___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__21;
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1;
static lean_object* l_Lean_Message_toString___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__6;
static lean_object* l_Lean_MessageData_ofSyntax___closed__1;
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__3;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataName;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lambda__2___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__23;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__7;
static lean_object* l_Lean_mkErrorStringWithPos___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__14;
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120_(uint8_t, uint8_t);
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__2;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7;
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___closed__5;
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__1;
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_instInhabitedMessageLog___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_paren___closed__2;
static lean_object* l_Lean_instInhabitedMessage___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4;
static lean_object* l_Lean_KernelException_toMessageData___closed__27;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeNameMessageData;
LEAN_EXPORT lean_object* l_Lean_stringToMessageData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeFormatMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object*);
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_mkErrorStringWithPos___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lean_mkErrorStringWithPos___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = l_Nat_repr(x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_string_append(x_11, x_7);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_string_append(x_15, x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_string_append(x_16, x_5);
x_18 = l_Lean_mkErrorStringWithPos___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_3);
x_21 = lean_string_append(x_20, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = l_Nat_repr(x_23);
x_25 = l_Lean_mkErrorStringWithPos___closed__4;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = lean_string_append(x_26, x_7);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Nat_repr(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = lean_string_append(x_30, x_5);
x_32 = lean_string_append(x_16, x_31);
lean_dec(x_31);
x_33 = l_Lean_mkErrorStringWithPos___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_3);
x_36 = lean_string_append(x_35, x_5);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_MessageSeverity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageSeverity_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageSeverity_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageSeverity_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageSeverity_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_MessageSeverity_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_MessageSeverity_toCtorIdx(x_1);
x_4 = l_Lean_MessageSeverity_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqMessageSeverity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_120____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqMessageSeverity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqMessageSeverity___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_PPFormat_hasSyntheticSorry___default(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PPFormat_hasSyntheticSorry___default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PPFormat_hasSyntheticSorry___default(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isEmpty(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_Format_isEmpty(x_2);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 2:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
case 6:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
x_1 = x_6;
goto _start;
}
case 7:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_MessageData_isEmpty(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_9;
goto _start;
}
}
case 9:
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
default: 
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 1);
x_1 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_MessageData_hasTag(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_2 = x_3;
goto _start;
}
case 4:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
case 7:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_MessageData_hasTag(x_1, x_11);
if (x_13 == 0)
{
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
}
case 8:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_1);
x_21 = 1;
return x_21;
}
}
case 9:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
x_25 = lean_apply_1(x_1, x_22);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_1);
x_27 = l_Lean_MessageData_hasTag(x_1, x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_24);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_1);
x_31 = 0;
return x_31;
}
else
{
size_t x_32; size_t x_33; uint8_t x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_34 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(x_1, x_24, x_32, x_33);
lean_dec(x_24);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_1);
x_35 = 1;
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_36 = 1;
return x_36;
}
}
default: 
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = 0;
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_hasTag(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MessageData_nil() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_mkPPContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_formatStxAux(x_4, x_5, x_6, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_ppTerm(x_11, x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = l_Lean_Syntax_copyHeadTailInfoFrom(x_1, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_MessageData_ofSyntax___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofSyntax___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_ppExprWithInfos(x_9, x_1, x_3);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_instantiateMVarsCore(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Expr_hasSyntheticSorry(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lambda__2___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofExpr___lambda__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Level_format(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__3;
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__4;
x_4 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__5;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = lean_box(x_3);
return x_4;
}
case 1:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__6;
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
}
case 2:
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_1 = x_18;
x_2 = x_16;
goto _start;
}
case 6:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
case 7:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_22);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_1);
x_27 = 1;
x_28 = lean_box(x_27);
return x_28;
}
}
case 9:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_1);
x_31 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_29);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_array_get_size(x_30);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_1);
x_36 = 0;
x_37 = lean_box(x_36);
return x_37;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_1, x_30, x_38, x_39);
lean_dec(x_30);
x_41 = lean_box(x_40);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_30);
lean_dec(x_1);
x_42 = 1;
x_43 = lean_box(x_42);
return x_43;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_2 = x_44;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_MessageData_formatAux(x_1, x_2, x_9, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_MessageData_formatAux(x_1, x_2, x_9, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_MessageData_formatAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("goal ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkErrorStringWithPos___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lean_Expr_mvar___override(x_22);
x_24 = lean_expr_dbg_to_string(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_formatAux___closed__2;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_2 = x_31;
x_3 = x_30;
goto _start;
}
case 4:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_1 = x_33;
x_3 = x_34;
goto _start;
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = l_Lean_MessageData_formatAux(x_1, x_2, x_37, x_4);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_nat_to_int(x_36);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_nat_to_int(x_36);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_36);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = l_Lean_MessageData_formatAux(x_1, x_2, x_52, x_4);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = 0;
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = 0;
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_53);
if (x_63 == 0)
{
return x_53;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_53, 0);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_53);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 7:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
lean_dec(x_3);
lean_inc(x_1);
x_69 = l_Lean_MessageData_formatAux(x_1, x_2, x_67, x_4);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_MessageData_formatAux(x_1, x_2, x_68, x_71);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_70);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
return x_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_68);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
return x_69;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 8:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_3 = x_88;
goto _start;
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_inc(x_92);
lean_dec(x_3);
lean_inc(x_1);
x_93 = l_Lean_MessageData_formatAux(x_1, x_2, x_91, x_4);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; size_t x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = 1;
x_97 = l_Lean_Name_toString(x_90, x_96);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_MessageData_formatAux___closed__4;
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_MessageData_formatAux___closed__6;
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_MessageData_formatAux___closed__7;
x_104 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_94);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_MessageData_formatAux___closed__8;
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_get_size(x_92);
x_109 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_110 = 0;
x_111 = l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1(x_1, x_2, x_109, x_110, x_92, x_95);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_array_to_list(lean_box(0), x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_MessageData_formatAux___closed__10;
x_117 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_115, x_116);
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_103);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_111, 0, x_118);
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_121 = lean_array_to_list(lean_box(0), x_119);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_107);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_MessageData_formatAux___closed__10;
x_124 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_122, x_123);
x_125 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_125, 0, x_103);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_120);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_107);
x_127 = !lean_is_exclusive(x_111);
if (x_127 == 0)
{
return x_111;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_111, 0);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_111);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_93);
if (x_131 == 0)
{
return x_93;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_93, 0);
x_133 = lean_ctor_get(x_93, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_93);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_3, 0);
lean_inc(x_135);
lean_dec(x_3);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
return x_136;
}
case 1:
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_2, 0);
x_139 = lean_ctor_get(x_3, 0);
lean_inc(x_139);
lean_dec(x_3);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_MessageData_mkPPContext(x_1, x_138);
lean_dec(x_138);
lean_dec(x_1);
lean_ctor_set(x_2, 0, x_141);
x_142 = lean_apply_2(x_140, x_2, x_4);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
lean_ctor_set(x_142, 0, x_145);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
return x_142;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_142, 0);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_142);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_2, 0);
lean_inc(x_154);
lean_dec(x_2);
x_155 = lean_ctor_get(x_3, 0);
lean_inc(x_155);
lean_dec(x_3);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_MessageData_mkPPContext(x_1, x_154);
lean_dec(x_154);
lean_dec(x_1);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_apply_2(x_156, x_158, x_4);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
lean_dec(x_160);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_159, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_167 = x_159;
} else {
 lean_dec_ref(x_159);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
case 2:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_2, 0);
lean_inc(x_169);
lean_dec(x_2);
x_170 = lean_ctor_get(x_3, 0);
lean_inc(x_170);
lean_dec(x_3);
x_171 = l_Lean_MessageData_mkPPContext(x_1, x_169);
lean_dec(x_169);
lean_dec(x_1);
x_172 = l_Lean_ppGoal(x_171, x_170, x_4);
return x_172;
}
case 3:
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_2);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_2, 0);
lean_dec(x_174);
x_175 = lean_ctor_get(x_3, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_175);
x_3 = x_176;
goto _start;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_2);
x_178 = lean_ctor_get(x_3, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_3, 1);
lean_inc(x_179);
lean_dec(x_3);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_178);
x_2 = x_180;
x_3 = x_179;
goto _start;
}
}
case 4:
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_1);
x_182 = lean_ctor_get(x_3, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_3, 1);
lean_inc(x_183);
lean_dec(x_3);
x_1 = x_182;
x_3 = x_183;
goto _start;
}
case 5:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_3, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_3, 1);
lean_inc(x_186);
lean_dec(x_3);
x_187 = l_Lean_MessageData_formatAux(x_1, x_2, x_186, x_4);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_nat_to_int(x_185);
x_191 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_187, 0, x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_187, 0);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_187);
x_194 = lean_nat_to_int(x_185);
x_195 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_193);
return x_196;
}
}
else
{
uint8_t x_197; 
lean_dec(x_185);
x_197 = !lean_is_exclusive(x_187);
if (x_197 == 0)
{
return x_187;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_187, 0);
x_199 = lean_ctor_get(x_187, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_187);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
case 6:
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_3, 0);
lean_inc(x_201);
lean_dec(x_3);
x_202 = l_Lean_MessageData_formatAux(x_1, x_2, x_201, x_4);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = 0;
x_206 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_205);
lean_ctor_set(x_202, 0, x_206);
return x_202;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_202, 0);
x_208 = lean_ctor_get(x_202, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_202);
x_209 = 0;
x_210 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_202);
if (x_212 == 0)
{
return x_202;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_202, 0);
x_214 = lean_ctor_get(x_202, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_202);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
case 7:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_3, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_3, 1);
lean_inc(x_217);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_218 = l_Lean_MessageData_formatAux(x_1, x_2, x_216, x_4);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_MessageData_formatAux(x_1, x_2, x_217, x_220);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_221, 0, x_224);
return x_221;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_221);
x_227 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_225);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
uint8_t x_229; 
lean_dec(x_219);
x_229 = !lean_is_exclusive(x_221);
if (x_229 == 0)
{
return x_221;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_221, 0);
x_231 = lean_ctor_get(x_221, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_221);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_217);
lean_dec(x_2);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_218);
if (x_233 == 0)
{
return x_218;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_218, 0);
x_235 = lean_ctor_get(x_218, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_218);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
case 8:
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_3, 1);
lean_inc(x_237);
lean_dec(x_3);
x_3 = x_237;
goto _start;
}
default: 
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_3, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_3, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_3, 2);
lean_inc(x_241);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_242 = l_Lean_MessageData_formatAux(x_1, x_2, x_240, x_4);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; size_t x_258; size_t x_259; lean_object* x_260; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = 1;
x_246 = l_Lean_Name_toString(x_239, x_245);
x_247 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l_Lean_MessageData_formatAux___closed__4;
x_249 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_MessageData_formatAux___closed__6;
x_251 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_MessageData_formatAux___closed__7;
x_253 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_243);
x_254 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lean_MessageData_formatAux___closed__8;
x_256 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_array_get_size(x_241);
x_258 = lean_usize_of_nat(x_257);
lean_dec(x_257);
x_259 = 0;
x_260 = l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2(x_1, x_2, x_258, x_259, x_241, x_244);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = lean_ctor_get(x_260, 0);
x_263 = lean_array_to_list(lean_box(0), x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_256);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_MessageData_formatAux___closed__10;
x_266 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_264, x_265);
x_267 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_267, 0, x_252);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set(x_260, 0, x_267);
return x_260;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_268 = lean_ctor_get(x_260, 0);
x_269 = lean_ctor_get(x_260, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_260);
x_270 = lean_array_to_list(lean_box(0), x_268);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_256);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_MessageData_formatAux___closed__10;
x_273 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_271, x_272);
x_274 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_274, 0, x_252);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_269);
return x_275;
}
}
else
{
uint8_t x_276; 
lean_dec(x_256);
x_276 = !lean_is_exclusive(x_260);
if (x_276 == 0)
{
return x_260;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_260, 0);
x_278 = lean_ctor_get(x_260, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_260);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_241);
lean_dec(x_239);
lean_dec(x_2);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_242);
if (x_280 == 0)
{
return x_242;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_242, 0);
x_282 = lean_ctor_get(x_242, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_242);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at_Lean_MessageData_formatAux___spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_MessageData_format___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_MessageData_format___closed__1;
x_5 = l_Lean_MessageData_formatAux(x_4, x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_format(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_Format_defWidth;
x_7 = lean_format_pretty(x_5, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = l_Std_Format_defWidth;
x_11 = lean_format_pretty(x_8, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppendMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeStringMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeStringMessageData___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeStringMessageData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeStringMessageData___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeStringMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_instCoeStringMessageData___closed__1;
x_2 = l_Lean_MessageData_instCoeStringMessageData___closed__2;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeStringMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeStringMessageData___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeFormatMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeLevelMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeLevelMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeLevelMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeExprMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeExprMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeExprMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeNameMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeNameMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeNameMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeSyntaxMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeSyntaxMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeSyntaxMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarIdMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("none", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeOptionExprMessageData___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeOptionExprMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExprMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeOptionExprMessageData___closed__3;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Lean_MessageData_arrayExpr_toMessageData___closed__3;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_MessageData_arrayExpr_toMessageData___closed__6;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_MessageData_ofExpr(x_8);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_12;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_MessageData_ofExpr(x_8);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#[", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeArrayExprMessageData___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeArrayExprMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExprMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MessageData_instCoeArrayExprMessageData___closed__3;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeArrayExprMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_MessageData_paren___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_paren___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_paren___closed__1;
x_3 = l_Lean_MessageData_paren___closed__2;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_formatAux___closed__3;
x_3 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = l_Lean_instInhabitedMessageData___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_MessageData_joinSep(x_4, x_2);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_ofList___closed__6;
x_2 = l_Lean_MessageData_ofList___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofList___closed__3;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_MessageData_ofList___closed__8;
x_4 = l_Lean_MessageData_joinSep(x_1, x_3);
x_5 = l_Lean_MessageData_formatAux___closed__3;
x_6 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_7 = l_Lean_MessageData_bracket(x_5, x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeListMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofList___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeListMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeListMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExprMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_1, x_2);
x_4 = l_Lean_MessageData_ofList(x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Message_endPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_Message_keepFullRange___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Message_severity___default() {
_start:
{
uint8_t x_1; 
x_1 = 2;
return x_1;
}
}
static lean_object* _init_l_Lean_Message_caption___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_mkErrorStringWithPos___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessage___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_mkErrorStringWithPos___closed__1;
x_3 = l_Lean_instInhabitedMessage___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = l_Lean_instInhabitedMessageData___closed__1;
x_7 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*5 + 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_instInhabitedMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessage___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Message_toString___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Message_toString___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Message_toString___lambda__2___closed__1;
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
x_9 = l_Lean_MessageData_formatAux___closed__9;
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
x_15 = l_Lean_MessageData_formatAux___closed__9;
x_16 = lean_string_append(x_1, x_15);
x_17 = lean_box(0);
x_18 = lean_apply_3(x_4, x_16, x_17, x_3);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Message_toString___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Message_toString___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Message_toString___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning: ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Message_toString___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error: ", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Message_toString___lambda__3___closed__1;
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
switch (x_7) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_3(x_6, x_3, x_8, x_5);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Message_toString___lambda__3___closed__2;
x_13 = l_Lean_mkErrorStringWithPos(x_10, x_11, x_12, x_2);
lean_dec(x_10);
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_3(x_6, x_14, x_15, x_5);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Message_toString___lambda__3___closed__3;
x_20 = l_Lean_mkErrorStringWithPos(x_17, x_18, x_19, x_2);
lean_dec(x_17);
x_21 = lean_string_append(x_20, x_3);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_apply_3(x_6, x_21, x_22, x_5);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Message_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":\n", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_MessageData_toString(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l_Lean_mkErrorStringWithPos___closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_2 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_11 = x_20;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_11 = x_21;
goto block_19;
}
block_19:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Message_toString___closed__1;
x_13 = lean_string_append(x_8, x_12);
x_14 = lean_string_append(x_13, x_6);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = l_Lean_Message_toString___lambda__3(x_1, x_11, x_14, x_15, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = l_Lean_Message_toString___lambda__3(x_1, x_11, x_6, x_17, x_7);
return x_18;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Message_toString___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Message_toString___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Message_toString___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Message_toString(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_MessageLog_msgs___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageLog_msgs___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageLog_msgs___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageLog_msgs___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_MessageLog_msgs___default___closed__2;
x_3 = l_Lean_MessageLog_msgs___default___closed__1;
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
static lean_object* _init_l_Lean_MessageLog_msgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_msgs___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedMessageLog___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_instInhabitedMessageLog___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_instInhabitedMessageLog___closed__2;
x_2 = l_Lean_instInhabitedMessageLog___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_instInhabitedMessageLog___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageLog___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_MessageLog_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_msgs___default___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentArray_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_push___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_append___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageLog_instAppendMessageLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_append), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageLog_instAppendMessageLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_instAppendMessageLog___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
lean_dec(x_5);
x_7 = lean_box(x_6);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(x_2, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = 0;
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(x_10, x_15, x_16);
lean_dec(x_10);
return x_17;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_box(x_12);
if (lean_obj_tag(x_17) == 2)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_5, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 0);
lean_dec(x_23);
x_24 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 1, x_24);
x_25 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_16;
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_10);
lean_ctor_set(x_28, 3, x_13);
lean_ctor_set(x_28, 4, x_14);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 1, x_27);
x_29 = lean_array_uset(x_7, x_2, x_28);
x_2 = x_16;
x_3 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_31 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_16;
x_3 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(x_5, x_6, x_3);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(x_10, x_11, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_17, x_18, x_15);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_22, x_23, x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_7, x_8, x_4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get_usize(x_1, 4);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Lean_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_10);
x_16 = lean_array_get_size(x_11);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_17, x_18, x_11);
x_20 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set_usize(x_20, 4, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(x_6, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_box(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_push___rarg(x_4, x_6);
x_2 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_11, x_16, x_17, x_2);
lean_dec(x_11);
return x_18;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_usize_shift_right(x_2, x_3);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_8, x_9, x_10, x_2);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_12, x_16, x_17, x_11);
lean_dec(x_12);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_nat_sub(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_19, x_24, x_25, x_2);
lean_dec(x_19);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_29, x_33, x_34, x_28);
lean_dec(x_29);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageLog_msgs___default___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forM___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageLog_forM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(x_6, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_11, x_16, x_17, x_2);
lean_dec(x_11);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_usize_shift_right(x_2, x_3);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_8, x_9, x_10, x_2);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_12, x_16, x_17, x_11);
lean_dec(x_12);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_nat_sub(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_19, x_24, x_25, x_2);
lean_dec(x_19);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_29, x_33, x_34, x_28);
lean_dec(x_29);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2, x_3);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_MessageData_ofList___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofExpr(x_1);
x_3 = l_Lean_indentD(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContext___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
x_2 = l_Lean_MessageLog_msgs___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__6;
x_8 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_4);
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_6);
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg___lambda__1), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg___lambda__2), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg___lambda__3), 7, 6);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_6);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg___lambda__4), 7, 6);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 10;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___rarg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_Lean_stringToMessageData___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_stringToMessageData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_7);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_10);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_12);
lean_inc(x_1);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_3 = x_13;
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_stringToMessageData___spec__3___at_Lean_stringToMessageData___spec__4(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_String_split___at_Lean_stringToMessageData___spec__1(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_stringToMessageData___spec__3___at_Lean_stringToMessageData___spec__4(x_2, x_3);
x_5 = l_Lean_MessageData_ofList___closed__7;
x_6 = l_Lean_MessageData_joinSep(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_Lean_stringToMessageData___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lean_stringToMessageData___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_Lean_stringToMessageData___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageData___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_instCoeStringMessageData___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageData___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeExprMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeLevelMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeNameMessageData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_stringToMessageData___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToMessageDataString___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataSyntax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeSyntaxMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofSyntax(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataTSyntax___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToMessageDataTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToMessageDataMessageData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___rarg(x_1, x_2, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___rarg(x_1, x_3, x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Array_ofSubarray___rarg(x_2);
x_4 = lean_array_to_list(lean_box(0), x_3);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___rarg(x_1, x_4, x_5);
x_7 = l_Lean_MessageData_ofList(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("some (", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOption___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOption___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_paren___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOption___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_MessageData_instCoeOptionExprMessageData___closed__3;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_instToMessageDataOption___rarg___closed__3;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_instToMessageDataOption___rarg___closed__5;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lean_MessageData_ofList___closed__6;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_MessageData_ofList___closed__7;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_paren___closed__1;
x_14 = l_Lean_MessageData_paren___closed__2;
x_15 = l_Lean_MessageData_bracket(x_13, x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<not-available>", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOptionExpr___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOptionExpr___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instToMessageDataOptionExpr___closed__3;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termM!_", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__1;
x_2 = l_Lean_termM_x21_____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("m!", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termM_x21_____closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStr", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__9;
x_2 = l_Lean_termM_x21_____closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termM_x21_____closed__5;
x_2 = l_Lean_termM_x21_____closed__7;
x_3 = l_Lean_termM_x21_____closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termM_x21_____closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_termM_x21_____closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termM_x21__() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_termM_x21_____closed__15;
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MessageData", 11);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__1;
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5;
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toMessageData", 13);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ToMessageData", 13);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termM_x21_____closed__1;
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12;
x_3 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termM_x21_____closed__3;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3;
lean_inc(x_13);
lean_inc(x_14);
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2;
x_18 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8;
lean_inc(x_12);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11;
x_21 = l_Lean_addMacroScope(x_14, x_20, x_13);
x_22 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10;
x_23 = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Lean_TSyntax_expandInterpolatedStr(x_9, x_19, x_24, x_2, x_3);
lean_dec(x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n\n", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_toMessageList___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = l_Lean_toMessageList___closed__2;
x_4 = l_Lean_MessageData_joinSep(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_indentD(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_KernelException_mkCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_MessageData_hasSyntheticSorry_visit___closed__6;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) unknown constant '", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) constant has already been declared '", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) declaration type mismatch", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) declaration type mismatch, '", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has type", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nbut it is expected to have type", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkErrorStringWithPos___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) declaration has metavariables '", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) declaration has free variables '", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) function expected", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) type expected", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) let-declaration type mismatch '", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) type mismatch at", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("application type mismatch", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__29;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nargument has type", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__31;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nbut function has type", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__33;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) invalid projection", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__35;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__37;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) deterministic timeout", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__39;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__40;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) excessive memory consumption detected", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__42;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__43;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) deep recursion detected", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__45;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__46;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(kernel) interrupted", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__48;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__49;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_KernelException_toMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_MessageData_ofName(x_4);
x_6 = l_Lean_KernelException_toMessageData___closed__2;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_KernelException_toMessageData___closed__4;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_11 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_3, x_10, x_2, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = l_Lean_KernelException_toMessageData___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_KernelException_toMessageData___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_20 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_12, x_19, x_2, x_18);
return x_20;
}
case 2:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_MessageData_ofName(x_26);
x_29 = l_Lean_KernelException_toMessageData___closed__11;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_KernelException_toMessageData___closed__13;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_25);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_KernelException_toMessageData___closed__15;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_27);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_KernelException_toMessageData___closed__16;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_42 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_24, x_41, x_2, x_40);
return x_42;
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
lean_dec(x_44);
x_49 = l_Lean_MessageData_ofName(x_47);
x_50 = l_Lean_KernelException_toMessageData___closed__11;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_KernelException_toMessageData___closed__13;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_46);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_KernelException_toMessageData___closed__15;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_indentExpr(x_48);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_KernelException_toMessageData___closed__16;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_63 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_45, x_62, x_2, x_61);
return x_63;
}
default: 
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_21);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_66 = l_Lean_KernelException_toMessageData___closed__9;
x_67 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_64, x_65, x_2, x_66);
return x_67;
}
}
}
case 3:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_MessageData_ofName(x_69);
x_71 = l_Lean_KernelException_toMessageData___closed__18;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_KernelException_toMessageData___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_76 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_68, x_75, x_2, x_74);
return x_76;
}
case 4:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l_Lean_MessageData_ofName(x_78);
x_80 = l_Lean_KernelException_toMessageData___closed__20;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_KernelException_toMessageData___closed__4;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2;
x_85 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_77, x_84, x_2, x_83);
return x_85;
}
case 5:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
lean_dec(x_1);
x_89 = l_Lean_indentExpr(x_88);
x_90 = l_Lean_KernelException_toMessageData___closed__22;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_KernelException_toMessageData___closed__16;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_86, x_87, x_2, x_93);
return x_94;
}
case 6:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 2);
lean_inc(x_97);
lean_dec(x_1);
x_98 = l_Lean_indentExpr(x_97);
x_99 = l_Lean_KernelException_toMessageData___closed__24;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_KernelException_toMessageData___closed__16;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_95, x_96, x_2, x_102);
return x_103;
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_MessageData_ofName(x_106);
x_108 = l_Lean_KernelException_toMessageData___closed__26;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_KernelException_toMessageData___closed__4;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_104, x_105, x_2, x_111);
return x_112;
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
lean_dec(x_1);
x_116 = l_Lean_indentExpr(x_115);
x_117 = l_Lean_KernelException_toMessageData___closed__28;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_KernelException_toMessageData___closed__16;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_113, x_114, x_2, x_120);
return x_121;
}
case 9:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_122 = lean_ctor_get(x_1, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_1, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 4);
lean_inc(x_126);
lean_dec(x_1);
x_127 = l_Lean_indentExpr(x_124);
x_128 = l_Lean_KernelException_toMessageData___closed__30;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_KernelException_toMessageData___closed__32;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_indentExpr(x_126);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_KernelException_toMessageData___closed__34;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_indentExpr(x_125);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_KernelException_toMessageData___closed__16;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_122, x_123, x_2, x_139);
return x_140;
}
case 10:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_1, 2);
lean_inc(x_143);
lean_dec(x_1);
x_144 = l_Lean_indentExpr(x_143);
x_145 = l_Lean_KernelException_toMessageData___closed__36;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_KernelException_toMessageData___closed__16;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_141, x_142, x_2, x_148);
return x_149;
}
case 11:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
x_150 = lean_ctor_get(x_1, 0);
lean_inc(x_150);
lean_dec(x_1);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = l_Lean_KernelException_toMessageData___closed__38;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_KernelException_toMessageData___closed__16;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
case 12:
{
lean_object* x_156; 
lean_dec(x_2);
x_156 = l_Lean_KernelException_toMessageData___closed__41;
return x_156;
}
case 13:
{
lean_object* x_157; 
lean_dec(x_2);
x_157 = l_Lean_KernelException_toMessageData___closed__44;
return x_157;
}
case 14:
{
lean_object* x_158; 
lean_dec(x_2);
x_158 = l_Lean_KernelException_toMessageData___closed__47;
return x_158;
}
default: 
{
lean_object* x_159; 
lean_dec(x_2);
x_159 = l_Lean_KernelException_toMessageData___closed__50;
return x_159;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PPExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Message(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkErrorStringWithPos___closed__1 = _init_l_Lean_mkErrorStringWithPos___closed__1();
lean_mark_persistent(l_Lean_mkErrorStringWithPos___closed__1);
l_Lean_mkErrorStringWithPos___closed__2 = _init_l_Lean_mkErrorStringWithPos___closed__2();
lean_mark_persistent(l_Lean_mkErrorStringWithPos___closed__2);
l_Lean_mkErrorStringWithPos___closed__3 = _init_l_Lean_mkErrorStringWithPos___closed__3();
lean_mark_persistent(l_Lean_mkErrorStringWithPos___closed__3);
l_Lean_mkErrorStringWithPos___closed__4 = _init_l_Lean_mkErrorStringWithPos___closed__4();
lean_mark_persistent(l_Lean_mkErrorStringWithPos___closed__4);
l_Lean_MessageSeverity_noConfusion___rarg___closed__1 = _init_l_Lean_MessageSeverity_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_MessageSeverity_noConfusion___rarg___closed__1);
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instBEqMessageSeverity___closed__1 = _init_l_Lean_instBEqMessageSeverity___closed__1();
lean_mark_persistent(l_Lean_instBEqMessageSeverity___closed__1);
l_Lean_instBEqMessageSeverity = _init_l_Lean_instBEqMessageSeverity();
lean_mark_persistent(l_Lean_instBEqMessageSeverity);
l_Lean_instInhabitedMessageData___closed__1 = _init_l_Lean_instInhabitedMessageData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedMessageData___closed__1);
l_Lean_instInhabitedMessageData = _init_l_Lean_instInhabitedMessageData();
lean_mark_persistent(l_Lean_instInhabitedMessageData);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
l_Lean_MessageData_ofSyntax___closed__1 = _init_l_Lean_MessageData_ofSyntax___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofSyntax___closed__1);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__1 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__1();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__1);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__2 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__2();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__2);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__3 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__3();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__3);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__4 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__4();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__4);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__5 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__5();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__5);
l_Lean_MessageData_hasSyntheticSorry_visit___closed__6 = _init_l_Lean_MessageData_hasSyntheticSorry_visit___closed__6();
lean_mark_persistent(l_Lean_MessageData_hasSyntheticSorry_visit___closed__6);
l_Lean_MessageData_formatAux___closed__1 = _init_l_Lean_MessageData_formatAux___closed__1();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__1);
l_Lean_MessageData_formatAux___closed__2 = _init_l_Lean_MessageData_formatAux___closed__2();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__2);
l_Lean_MessageData_formatAux___closed__3 = _init_l_Lean_MessageData_formatAux___closed__3();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__3);
l_Lean_MessageData_formatAux___closed__4 = _init_l_Lean_MessageData_formatAux___closed__4();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__4);
l_Lean_MessageData_formatAux___closed__5 = _init_l_Lean_MessageData_formatAux___closed__5();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__5);
l_Lean_MessageData_formatAux___closed__6 = _init_l_Lean_MessageData_formatAux___closed__6();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__6);
l_Lean_MessageData_formatAux___closed__7 = _init_l_Lean_MessageData_formatAux___closed__7();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__7);
l_Lean_MessageData_formatAux___closed__8 = _init_l_Lean_MessageData_formatAux___closed__8();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__8);
l_Lean_MessageData_formatAux___closed__9 = _init_l_Lean_MessageData_formatAux___closed__9();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__9);
l_Lean_MessageData_formatAux___closed__10 = _init_l_Lean_MessageData_formatAux___closed__10();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__10);
l_Lean_MessageData_format___closed__1 = _init_l_Lean_MessageData_format___closed__1();
lean_mark_persistent(l_Lean_MessageData_format___closed__1);
l_Lean_MessageData_instCoeStringMessageData___closed__1 = _init_l_Lean_MessageData_instCoeStringMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeStringMessageData___closed__1);
l_Lean_MessageData_instCoeStringMessageData___closed__2 = _init_l_Lean_MessageData_instCoeStringMessageData___closed__2();
lean_mark_persistent(l_Lean_MessageData_instCoeStringMessageData___closed__2);
l_Lean_MessageData_instCoeStringMessageData___closed__3 = _init_l_Lean_MessageData_instCoeStringMessageData___closed__3();
lean_mark_persistent(l_Lean_MessageData_instCoeStringMessageData___closed__3);
l_Lean_MessageData_instCoeStringMessageData = _init_l_Lean_MessageData_instCoeStringMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeStringMessageData);
l_Lean_MessageData_instCoeLevelMessageData___closed__1 = _init_l_Lean_MessageData_instCoeLevelMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeLevelMessageData___closed__1);
l_Lean_MessageData_instCoeLevelMessageData = _init_l_Lean_MessageData_instCoeLevelMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeLevelMessageData);
l_Lean_MessageData_instCoeExprMessageData___closed__1 = _init_l_Lean_MessageData_instCoeExprMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeExprMessageData___closed__1);
l_Lean_MessageData_instCoeExprMessageData = _init_l_Lean_MessageData_instCoeExprMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeExprMessageData);
l_Lean_MessageData_instCoeNameMessageData___closed__1 = _init_l_Lean_MessageData_instCoeNameMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeNameMessageData___closed__1);
l_Lean_MessageData_instCoeNameMessageData = _init_l_Lean_MessageData_instCoeNameMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeNameMessageData);
l_Lean_MessageData_instCoeSyntaxMessageData___closed__1 = _init_l_Lean_MessageData_instCoeSyntaxMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeSyntaxMessageData___closed__1);
l_Lean_MessageData_instCoeSyntaxMessageData = _init_l_Lean_MessageData_instCoeSyntaxMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeSyntaxMessageData);
l_Lean_MessageData_instCoeOptionExprMessageData___closed__1 = _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeOptionExprMessageData___closed__1);
l_Lean_MessageData_instCoeOptionExprMessageData___closed__2 = _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__2();
lean_mark_persistent(l_Lean_MessageData_instCoeOptionExprMessageData___closed__2);
l_Lean_MessageData_instCoeOptionExprMessageData___closed__3 = _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__3();
lean_mark_persistent(l_Lean_MessageData_instCoeOptionExprMessageData___closed__3);
l_Lean_MessageData_arrayExpr_toMessageData___closed__1 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__1);
l_Lean_MessageData_arrayExpr_toMessageData___closed__2 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__2();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__2);
l_Lean_MessageData_arrayExpr_toMessageData___closed__3 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
l_Lean_MessageData_arrayExpr_toMessageData___closed__4 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__4();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__4);
l_Lean_MessageData_arrayExpr_toMessageData___closed__5 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__5();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__5);
l_Lean_MessageData_arrayExpr_toMessageData___closed__6 = _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__6();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___closed__6);
l_Lean_MessageData_instCoeArrayExprMessageData___closed__1 = _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeArrayExprMessageData___closed__1);
l_Lean_MessageData_instCoeArrayExprMessageData___closed__2 = _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__2();
lean_mark_persistent(l_Lean_MessageData_instCoeArrayExprMessageData___closed__2);
l_Lean_MessageData_instCoeArrayExprMessageData___closed__3 = _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__3();
lean_mark_persistent(l_Lean_MessageData_instCoeArrayExprMessageData___closed__3);
l_Lean_MessageData_paren___closed__1 = _init_l_Lean_MessageData_paren___closed__1();
lean_mark_persistent(l_Lean_MessageData_paren___closed__1);
l_Lean_MessageData_paren___closed__2 = _init_l_Lean_MessageData_paren___closed__2();
lean_mark_persistent(l_Lean_MessageData_paren___closed__2);
l_Lean_MessageData_ofList___closed__1 = _init_l_Lean_MessageData_ofList___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__1);
l_Lean_MessageData_ofList___closed__2 = _init_l_Lean_MessageData_ofList___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__2);
l_Lean_MessageData_ofList___closed__3 = _init_l_Lean_MessageData_ofList___closed__3();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__3);
l_Lean_MessageData_ofList___closed__4 = _init_l_Lean_MessageData_ofList___closed__4();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__4);
l_Lean_MessageData_ofList___closed__5 = _init_l_Lean_MessageData_ofList___closed__5();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__5);
l_Lean_MessageData_ofList___closed__6 = _init_l_Lean_MessageData_ofList___closed__6();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__6);
l_Lean_MessageData_ofList___closed__7 = _init_l_Lean_MessageData_ofList___closed__7();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__7);
l_Lean_MessageData_ofList___closed__8 = _init_l_Lean_MessageData_ofList___closed__8();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__8);
l_Lean_MessageData_instCoeListMessageData___closed__1 = _init_l_Lean_MessageData_instCoeListMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeListMessageData___closed__1);
l_Lean_MessageData_instCoeListMessageData = _init_l_Lean_MessageData_instCoeListMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeListMessageData);
l_Lean_Message_endPos___default = _init_l_Lean_Message_endPos___default();
lean_mark_persistent(l_Lean_Message_endPos___default);
l_Lean_Message_keepFullRange___default = _init_l_Lean_Message_keepFullRange___default();
l_Lean_Message_severity___default = _init_l_Lean_Message_severity___default();
l_Lean_Message_caption___default = _init_l_Lean_Message_caption___default();
lean_mark_persistent(l_Lean_Message_caption___default);
l_Lean_instInhabitedMessage___closed__1 = _init_l_Lean_instInhabitedMessage___closed__1();
lean_mark_persistent(l_Lean_instInhabitedMessage___closed__1);
l_Lean_instInhabitedMessage___closed__2 = _init_l_Lean_instInhabitedMessage___closed__2();
lean_mark_persistent(l_Lean_instInhabitedMessage___closed__2);
l_Lean_instInhabitedMessage = _init_l_Lean_instInhabitedMessage();
lean_mark_persistent(l_Lean_instInhabitedMessage);
l_Lean_Message_toString___lambda__2___closed__1 = _init_l_Lean_Message_toString___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Message_toString___lambda__2___closed__1);
l_Lean_Message_toString___lambda__3___closed__1 = _init_l_Lean_Message_toString___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Message_toString___lambda__3___closed__1);
l_Lean_Message_toString___lambda__3___closed__2 = _init_l_Lean_Message_toString___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Message_toString___lambda__3___closed__2);
l_Lean_Message_toString___lambda__3___closed__3 = _init_l_Lean_Message_toString___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Message_toString___lambda__3___closed__3);
l_Lean_Message_toString___closed__1 = _init_l_Lean_Message_toString___closed__1();
lean_mark_persistent(l_Lean_Message_toString___closed__1);
l_Lean_MessageLog_msgs___default___closed__1 = _init_l_Lean_MessageLog_msgs___default___closed__1();
lean_mark_persistent(l_Lean_MessageLog_msgs___default___closed__1);
l_Lean_MessageLog_msgs___default___closed__2 = _init_l_Lean_MessageLog_msgs___default___closed__2();
lean_mark_persistent(l_Lean_MessageLog_msgs___default___closed__2);
l_Lean_MessageLog_msgs___default___closed__3 = _init_l_Lean_MessageLog_msgs___default___closed__3();
lean_mark_persistent(l_Lean_MessageLog_msgs___default___closed__3);
l_Lean_MessageLog_msgs___default = _init_l_Lean_MessageLog_msgs___default();
lean_mark_persistent(l_Lean_MessageLog_msgs___default);
l_Lean_instInhabitedMessageLog___closed__1 = _init_l_Lean_instInhabitedMessageLog___closed__1();
lean_mark_persistent(l_Lean_instInhabitedMessageLog___closed__1);
l_Lean_instInhabitedMessageLog___closed__2 = _init_l_Lean_instInhabitedMessageLog___closed__2();
lean_mark_persistent(l_Lean_instInhabitedMessageLog___closed__2);
l_Lean_instInhabitedMessageLog___closed__3 = _init_l_Lean_instInhabitedMessageLog___closed__3();
l_Lean_instInhabitedMessageLog___closed__4 = _init_l_Lean_instInhabitedMessageLog___closed__4();
lean_mark_persistent(l_Lean_instInhabitedMessageLog___closed__4);
l_Lean_instInhabitedMessageLog = _init_l_Lean_instInhabitedMessageLog();
lean_mark_persistent(l_Lean_instInhabitedMessageLog);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
l_Lean_MessageLog_instAppendMessageLog___closed__1 = _init_l_Lean_MessageLog_instAppendMessageLog___closed__1();
lean_mark_persistent(l_Lean_MessageLog_instAppendMessageLog___closed__1);
l_Lean_MessageLog_instAppendMessageLog = _init_l_Lean_MessageLog_instAppendMessageLog();
lean_mark_persistent(l_Lean_MessageLog_instAppendMessageLog);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1);
l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1 = _init_l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1);
l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2 = _init_l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___rarg___lambda__1___closed__2);
l_Lean_instToMessageDataExpr = _init_l_Lean_instToMessageDataExpr();
lean_mark_persistent(l_Lean_instToMessageDataExpr);
l_Lean_instToMessageDataLevel = _init_l_Lean_instToMessageDataLevel();
lean_mark_persistent(l_Lean_instToMessageDataLevel);
l_Lean_instToMessageDataName = _init_l_Lean_instToMessageDataName();
lean_mark_persistent(l_Lean_instToMessageDataName);
l_Lean_instToMessageDataString___closed__1 = _init_l_Lean_instToMessageDataString___closed__1();
lean_mark_persistent(l_Lean_instToMessageDataString___closed__1);
l_Lean_instToMessageDataString = _init_l_Lean_instToMessageDataString();
lean_mark_persistent(l_Lean_instToMessageDataString);
l_Lean_instToMessageDataSyntax = _init_l_Lean_instToMessageDataSyntax();
lean_mark_persistent(l_Lean_instToMessageDataSyntax);
l_Lean_instToMessageDataMessageData___closed__1 = _init_l_Lean_instToMessageDataMessageData___closed__1();
lean_mark_persistent(l_Lean_instToMessageDataMessageData___closed__1);
l_Lean_instToMessageDataMessageData = _init_l_Lean_instToMessageDataMessageData();
lean_mark_persistent(l_Lean_instToMessageDataMessageData);
l_Lean_instToMessageDataOption___rarg___closed__1 = _init_l_Lean_instToMessageDataOption___rarg___closed__1();
lean_mark_persistent(l_Lean_instToMessageDataOption___rarg___closed__1);
l_Lean_instToMessageDataOption___rarg___closed__2 = _init_l_Lean_instToMessageDataOption___rarg___closed__2();
lean_mark_persistent(l_Lean_instToMessageDataOption___rarg___closed__2);
l_Lean_instToMessageDataOption___rarg___closed__3 = _init_l_Lean_instToMessageDataOption___rarg___closed__3();
lean_mark_persistent(l_Lean_instToMessageDataOption___rarg___closed__3);
l_Lean_instToMessageDataOption___rarg___closed__4 = _init_l_Lean_instToMessageDataOption___rarg___closed__4();
lean_mark_persistent(l_Lean_instToMessageDataOption___rarg___closed__4);
l_Lean_instToMessageDataOption___rarg___closed__5 = _init_l_Lean_instToMessageDataOption___rarg___closed__5();
lean_mark_persistent(l_Lean_instToMessageDataOption___rarg___closed__5);
l_Lean_instToMessageDataOptionExpr___closed__1 = _init_l_Lean_instToMessageDataOptionExpr___closed__1();
lean_mark_persistent(l_Lean_instToMessageDataOptionExpr___closed__1);
l_Lean_instToMessageDataOptionExpr___closed__2 = _init_l_Lean_instToMessageDataOptionExpr___closed__2();
lean_mark_persistent(l_Lean_instToMessageDataOptionExpr___closed__2);
l_Lean_instToMessageDataOptionExpr___closed__3 = _init_l_Lean_instToMessageDataOptionExpr___closed__3();
lean_mark_persistent(l_Lean_instToMessageDataOptionExpr___closed__3);
l_Lean_termM_x21_____closed__1 = _init_l_Lean_termM_x21_____closed__1();
lean_mark_persistent(l_Lean_termM_x21_____closed__1);
l_Lean_termM_x21_____closed__2 = _init_l_Lean_termM_x21_____closed__2();
lean_mark_persistent(l_Lean_termM_x21_____closed__2);
l_Lean_termM_x21_____closed__3 = _init_l_Lean_termM_x21_____closed__3();
lean_mark_persistent(l_Lean_termM_x21_____closed__3);
l_Lean_termM_x21_____closed__4 = _init_l_Lean_termM_x21_____closed__4();
lean_mark_persistent(l_Lean_termM_x21_____closed__4);
l_Lean_termM_x21_____closed__5 = _init_l_Lean_termM_x21_____closed__5();
lean_mark_persistent(l_Lean_termM_x21_____closed__5);
l_Lean_termM_x21_____closed__6 = _init_l_Lean_termM_x21_____closed__6();
lean_mark_persistent(l_Lean_termM_x21_____closed__6);
l_Lean_termM_x21_____closed__7 = _init_l_Lean_termM_x21_____closed__7();
lean_mark_persistent(l_Lean_termM_x21_____closed__7);
l_Lean_termM_x21_____closed__8 = _init_l_Lean_termM_x21_____closed__8();
lean_mark_persistent(l_Lean_termM_x21_____closed__8);
l_Lean_termM_x21_____closed__9 = _init_l_Lean_termM_x21_____closed__9();
lean_mark_persistent(l_Lean_termM_x21_____closed__9);
l_Lean_termM_x21_____closed__10 = _init_l_Lean_termM_x21_____closed__10();
lean_mark_persistent(l_Lean_termM_x21_____closed__10);
l_Lean_termM_x21_____closed__11 = _init_l_Lean_termM_x21_____closed__11();
lean_mark_persistent(l_Lean_termM_x21_____closed__11);
l_Lean_termM_x21_____closed__12 = _init_l_Lean_termM_x21_____closed__12();
lean_mark_persistent(l_Lean_termM_x21_____closed__12);
l_Lean_termM_x21_____closed__13 = _init_l_Lean_termM_x21_____closed__13();
lean_mark_persistent(l_Lean_termM_x21_____closed__13);
l_Lean_termM_x21_____closed__14 = _init_l_Lean_termM_x21_____closed__14();
lean_mark_persistent(l_Lean_termM_x21_____closed__14);
l_Lean_termM_x21_____closed__15 = _init_l_Lean_termM_x21_____closed__15();
lean_mark_persistent(l_Lean_termM_x21_____closed__15);
l_Lean_termM_x21__ = _init_l_Lean_termM_x21__();
lean_mark_persistent(l_Lean_termM_x21__);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__13);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__14);
l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15 = _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15();
lean_mark_persistent(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__15);
l_Lean_toMessageList___closed__1 = _init_l_Lean_toMessageList___closed__1();
lean_mark_persistent(l_Lean_toMessageList___closed__1);
l_Lean_toMessageList___closed__2 = _init_l_Lean_toMessageList___closed__2();
lean_mark_persistent(l_Lean_toMessageList___closed__2);
l_Lean_KernelException_toMessageData___closed__1 = _init_l_Lean_KernelException_toMessageData___closed__1();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__1);
l_Lean_KernelException_toMessageData___closed__2 = _init_l_Lean_KernelException_toMessageData___closed__2();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__2);
l_Lean_KernelException_toMessageData___closed__3 = _init_l_Lean_KernelException_toMessageData___closed__3();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__3);
l_Lean_KernelException_toMessageData___closed__4 = _init_l_Lean_KernelException_toMessageData___closed__4();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__4);
l_Lean_KernelException_toMessageData___closed__5 = _init_l_Lean_KernelException_toMessageData___closed__5();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__5);
l_Lean_KernelException_toMessageData___closed__6 = _init_l_Lean_KernelException_toMessageData___closed__6();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__6);
l_Lean_KernelException_toMessageData___closed__7 = _init_l_Lean_KernelException_toMessageData___closed__7();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__7);
l_Lean_KernelException_toMessageData___closed__8 = _init_l_Lean_KernelException_toMessageData___closed__8();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__8);
l_Lean_KernelException_toMessageData___closed__9 = _init_l_Lean_KernelException_toMessageData___closed__9();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__9);
l_Lean_KernelException_toMessageData___closed__10 = _init_l_Lean_KernelException_toMessageData___closed__10();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__10);
l_Lean_KernelException_toMessageData___closed__11 = _init_l_Lean_KernelException_toMessageData___closed__11();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__11);
l_Lean_KernelException_toMessageData___closed__12 = _init_l_Lean_KernelException_toMessageData___closed__12();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__12);
l_Lean_KernelException_toMessageData___closed__13 = _init_l_Lean_KernelException_toMessageData___closed__13();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__13);
l_Lean_KernelException_toMessageData___closed__14 = _init_l_Lean_KernelException_toMessageData___closed__14();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__14);
l_Lean_KernelException_toMessageData___closed__15 = _init_l_Lean_KernelException_toMessageData___closed__15();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__15);
l_Lean_KernelException_toMessageData___closed__16 = _init_l_Lean_KernelException_toMessageData___closed__16();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__16);
l_Lean_KernelException_toMessageData___closed__17 = _init_l_Lean_KernelException_toMessageData___closed__17();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__17);
l_Lean_KernelException_toMessageData___closed__18 = _init_l_Lean_KernelException_toMessageData___closed__18();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__18);
l_Lean_KernelException_toMessageData___closed__19 = _init_l_Lean_KernelException_toMessageData___closed__19();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__19);
l_Lean_KernelException_toMessageData___closed__20 = _init_l_Lean_KernelException_toMessageData___closed__20();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__20);
l_Lean_KernelException_toMessageData___closed__21 = _init_l_Lean_KernelException_toMessageData___closed__21();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__21);
l_Lean_KernelException_toMessageData___closed__22 = _init_l_Lean_KernelException_toMessageData___closed__22();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__22);
l_Lean_KernelException_toMessageData___closed__23 = _init_l_Lean_KernelException_toMessageData___closed__23();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__23);
l_Lean_KernelException_toMessageData___closed__24 = _init_l_Lean_KernelException_toMessageData___closed__24();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__24);
l_Lean_KernelException_toMessageData___closed__25 = _init_l_Lean_KernelException_toMessageData___closed__25();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__25);
l_Lean_KernelException_toMessageData___closed__26 = _init_l_Lean_KernelException_toMessageData___closed__26();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__26);
l_Lean_KernelException_toMessageData___closed__27 = _init_l_Lean_KernelException_toMessageData___closed__27();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__27);
l_Lean_KernelException_toMessageData___closed__28 = _init_l_Lean_KernelException_toMessageData___closed__28();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__28);
l_Lean_KernelException_toMessageData___closed__29 = _init_l_Lean_KernelException_toMessageData___closed__29();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__29);
l_Lean_KernelException_toMessageData___closed__30 = _init_l_Lean_KernelException_toMessageData___closed__30();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__30);
l_Lean_KernelException_toMessageData___closed__31 = _init_l_Lean_KernelException_toMessageData___closed__31();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__31);
l_Lean_KernelException_toMessageData___closed__32 = _init_l_Lean_KernelException_toMessageData___closed__32();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__32);
l_Lean_KernelException_toMessageData___closed__33 = _init_l_Lean_KernelException_toMessageData___closed__33();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__33);
l_Lean_KernelException_toMessageData___closed__34 = _init_l_Lean_KernelException_toMessageData___closed__34();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__34);
l_Lean_KernelException_toMessageData___closed__35 = _init_l_Lean_KernelException_toMessageData___closed__35();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__35);
l_Lean_KernelException_toMessageData___closed__36 = _init_l_Lean_KernelException_toMessageData___closed__36();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__36);
l_Lean_KernelException_toMessageData___closed__37 = _init_l_Lean_KernelException_toMessageData___closed__37();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__37);
l_Lean_KernelException_toMessageData___closed__38 = _init_l_Lean_KernelException_toMessageData___closed__38();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__38);
l_Lean_KernelException_toMessageData___closed__39 = _init_l_Lean_KernelException_toMessageData___closed__39();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__39);
l_Lean_KernelException_toMessageData___closed__40 = _init_l_Lean_KernelException_toMessageData___closed__40();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__40);
l_Lean_KernelException_toMessageData___closed__41 = _init_l_Lean_KernelException_toMessageData___closed__41();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__41);
l_Lean_KernelException_toMessageData___closed__42 = _init_l_Lean_KernelException_toMessageData___closed__42();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__42);
l_Lean_KernelException_toMessageData___closed__43 = _init_l_Lean_KernelException_toMessageData___closed__43();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__43);
l_Lean_KernelException_toMessageData___closed__44 = _init_l_Lean_KernelException_toMessageData___closed__44();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__44);
l_Lean_KernelException_toMessageData___closed__45 = _init_l_Lean_KernelException_toMessageData___closed__45();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__45);
l_Lean_KernelException_toMessageData___closed__46 = _init_l_Lean_KernelException_toMessageData___closed__46();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__46);
l_Lean_KernelException_toMessageData___closed__47 = _init_l_Lean_KernelException_toMessageData___closed__47();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__47);
l_Lean_KernelException_toMessageData___closed__48 = _init_l_Lean_KernelException_toMessageData___closed__48();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__48);
l_Lean_KernelException_toMessageData___closed__49 = _init_l_Lean_KernelException_toMessageData___closed__49();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__49);
l_Lean_KernelException_toMessageData___closed__50 = _init_l_Lean_KernelException_toMessageData___closed__50();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__50);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
