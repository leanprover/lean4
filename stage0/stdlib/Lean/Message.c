// Lean compiler output
// Module: Lean.Message
// Imports: Init Lean.Data.Position Lean.Data.OpenDecl Lean.Syntax Lean.MetavarContext Lean.Environment Lean.Util.PPExt
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
static lean_object* l_Lean_KernelException_toMessageData___closed__32;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__10;
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__1;
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102____boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_72____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11;
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__2;
lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__8;
uint8_t l_Lean_MessageData_isNest(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__19;
static lean_object* l_Lean_MessageData_instantiateMVars___closed__1;
static lean_object* l_Lean_instBEqMessageSeverity___closed__1;
static lean_object* l_Lean_termM_x21_____closed__1;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_hasErrors_match__1___rarg(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_MessageData_paren___closed__1;
static lean_object* l_Lean_MessageData_paren___closed__2;
lean_object* l_Lean_termM_x21__;
static lean_object* l_Lean_KernelException_toMessageData___closed__7;
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__6;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_MessageData_instCoeNameMessageData(lean_object*);
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
lean_object* l_Lean_MessageData_formatAux_match__1___rarg___boxed(lean_object**);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MessageData_formatAux_match__1(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__24;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_sbracket(lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_instCoeStringMessageData;
static lean_object* l_Lean_termM_x21_____closed__13;
lean_object* l_Lean_MessageLog_getInfoMessages_match__1(lean_object*);
static lean_object* l_Lean_Message_toString___lambda__3___closed__3;
static lean_object* l_Lean_MessageData_instantiateMVars___closed__4;
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
lean_object* l_Lean_MessageData_joinSep_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_isNil_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Lean_instBEqMessageSeverity;
lean_object* l_Lean_Message_toString___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_hasErrors_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList_match__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_instToMessageDataArray___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_instCoeFormatMessageData(lean_object*);
lean_object* l_Lean_instToMessageDataFormat(lean_object*);
static lean_object* l_Lean_instInhabitedMessageLog___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__1(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__16;
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__4;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__1;
lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData_match__2(lean_object*);
uint8_t l_Lean_Message_severity___default;
static lean_object* l_Lean_instInhabitedMessageLog___closed__2;
lean_object* l_Lean_MessageData_instCoeArrayExprMessageData(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
static lean_object* l_Lean_Message_toString___lambda__3___closed__1;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__5;
lean_object* l_Lean_Message_toString_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__2;
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_instAddMessageContext(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedMessageLog___closed__4;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__20;
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(uint8_t, uint8_t);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__4;
lean_object* l_Lean_addMessageContextFull___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__3;
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__22;
static lean_object* l_Lean_KernelException_toMessageData___closed__37;
static lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___closed__3;
static lean_object* l_Lean_MessageData_ofList___closed__5;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__5;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10;
lean_object* l_Lean_instToMessageDataLevel(lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
static lean_object* l_Lean_MessageLog_msgs___default___closed__2;
lean_object* l_Lean_MessageLog_getInfoMessages_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_Message_caption___default;
lean_object* l_Lean_MessageData_isNil_match__1(lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__6;
lean_object* l_Lean_Syntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16;
static lean_object* l_Lean_Message_toString___lambda__2___closed__1;
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData_match__1(lean_object*);
lean_object* l_Lean_MessageData_instAppendMessageData(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__29;
static lean_object* l_Lean_mkErrorStringWithPos___closed__4;
static lean_object* l_Lean_termM_x21_____closed__11;
lean_object* l_Lean_stringToMessageData___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataOption_match__1(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_instAppendMessageLog;
lean_object* l_Lean_instToMessageDataArray(lean_object*);
lean_object* l_Lean_instToMessageData(lean_object*);
lean_object* l_Lean_instInhabitedMessageData;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__7;
lean_object* l_Lean_Message_toString_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
uint8_t l_Lean_MessageData_isNil(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__25;
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___boxed(lean_object*);
lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__30;
lean_object* l_Lean_instToMessageData___rarg(lean_object*);
lean_object* l_Lean_Message_toString___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Message_toString___lambda__2___closed__2;
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__1;
lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__2(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(lean_object*, size_t, size_t);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_instToMessageDataString___closed__1;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedMessage;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__18;
lean_object* l_List_map___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__5;
uint32_t l_String_back(lean_object*);
uint8_t l_Lean_instInhabitedMessageSeverity;
lean_object* l_Lean_Message_toString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__12;
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataOptionExpr___boxed(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__33;
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__1;
lean_object* l_Lean_MessageData_isNest_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instantiateMVars___closed__3;
static lean_object* l_Lean_KernelException_toMessageData___closed__14;
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12;
static lean_object* l_Lean_KernelException_toMessageData___closed__28;
static lean_object* l_Lean_Message_toString___closed__1;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
static lean_object* l_Lean_instInhabitedMessage___closed__2;
lean_object* l_Lean_MessageData_instCoeSyntaxMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object*);
static lean_object* l_Lean_mkErrorStringWithPos___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(lean_object*, size_t, size_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataName(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(lean_object*, size_t, size_t);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5;
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14;
static lean_object* l_Lean_KernelException_toMessageData___closed__34;
lean_object* l_Lean_MessageData_instCoeLevelMessageData(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedMessage___closed__1;
static lean_object* l_Lean_termM_x21_____closed__10;
static lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15;
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataMessageData;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString_match__1(lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__27;
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataOption(lean_object*);
lean_object* l_Lean_KernelException_toMessageData_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataMessageData___closed__1;
lean_object* l_Lean_MessageData_ofList___boxed(lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars_visit_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_instCoeExprMessageData(lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__2;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__9;
lean_object* l_Lean_MessageData_instCoeListMessageDataMessageData;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__36;
size_t l_USize_land(size_t, size_t);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_format___closed__1;
lean_object* l_Lean_MessageData_ofArray(lean_object*);
lean_object* l_List_map___at_Lean_stringToMessageData___spec__3(lean_object*);
lean_object* l_Lean_MessageLog_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataOptionExpr(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__1;
lean_object* l_Lean_instToMessageDataList(lean_object*);
static lean_object* l_Lean_instToMessageDataOption___rarg___closed__3;
static lean_object* l_Lean_MessageData_sbracket___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Message_toString___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7;
static lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__8;
static lean_object* l_Lean_termM_x21_____closed__9;
lean_object* l_Lean_MessageLog_empty;
uint8_t l_String_isEmpty(lean_object*);
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData(lean_object*);
lean_object* l_Lean_instInhabitedMessageLog;
static lean_object* l_Lean_KernelException_toMessageData___closed__4;
lean_object* l_Lean_Message_toString___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageLog_msgs___default___closed__1;
lean_object* l_Lean_MessageData_ofList_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__17;
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_instToMessageDataExpr(lean_object*);
static lean_object* l_Lean_Message_toString___lambda__3___closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__38;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__21;
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasTag___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkErrorStringWithPos___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__16;
lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
lean_object* l_Std_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToMessageDataOptionExpr___closed__3;
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3;
static lean_object* l_Lean_KernelException_toMessageData___closed__2;
lean_object* l_Lean_MessageData_instCoeListExprMessageData(lean_object*);
static lean_object* l_Lean_mkErrorStringWithPos___closed__3;
static lean_object* l_Lean_MessageData_ofList___closed__4;
static lean_object* l_Lean_MessageData_ofList___closed__8;
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__7;
lean_object* l_Lean_Message_endPos___default;
lean_object* l_Lean_MessageData_joinSep___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2;
static lean_object* l_Lean_KernelException_toMessageData___closed__31;
lean_object* l_Lean_MessageLog_getInfoMessages_match__1___rarg(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__35;
static lean_object* l_Lean_termM_x21_____closed__5;
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_isNest___boxed(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__23;
lean_object* l_Lean_instToMessageDataList___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_hasErrors_match__1(lean_object*);
lean_object* l_Lean_instAddMessageContext___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedMessageData___closed__1;
lean_object* l_Lean_instToMessageDataOption___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasTag_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData_match__1(lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__4;
static lean_object* l_Lean_KernelException_toMessageData___closed__12;
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__1;
lean_object* l_Lean_MessageLog_msgs___default;
static lean_object* l_Lean_KernelException_toMessageData___closed__13;
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_termM_x21_____closed__15;
lean_object* l_Lean_mkErrorStringWithPos_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_forM(lean_object*);
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__3;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1;
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_termM_x21_____closed__14;
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToMessageDataString;
lean_object* l_Lean_MessageData_isNest_match__1___rarg(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_instInhabitedMessageLog___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__4;
lean_object* l_Lean_addMessageContextFull___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___closed__2;
lean_object* l___private_Lean_Message_0__Lean_KernelException_mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep_match__1(lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_KernelException_toMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6;
lean_object* l_Lean_MessageData_hasTag_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_MessageLog_isEmpty(lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Lean_KernelException_toMessageData___closed__26;
static lean_object* l_Lean_MessageLog_msgs___default___closed__3;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__3;
lean_object* l_Lean_instToMessageDataSyntax(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_mkErrorStringWithPos_match__1(lean_object*);
static lean_object* l_Lean_MessageLog_instAppendMessageLog___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13;
lean_object* l_Lean_Message_toString___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_formatAux___closed__2;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_addMessageContextPartial(lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_isNil___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofList___closed__1;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
static lean_object* l_Lean_KernelException_toMessageData___closed__11;
static lean_object* l_Lean_MessageData_instantiateMVars___closed__2;
static lean_object* l_Lean_MessageData_instCoeStringMessageData___closed__3;
static lean_object* l_Lean_termM_x21_____closed__6;
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars_visit(lean_object*, lean_object*);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_Lean_mkErrorStringWithPos_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkErrorStringWithPos_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": ");
return x_1;
}
}
static lean_object* _init_l_Lean_mkErrorStringWithPos___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-");
return x_1;
}
}
lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
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
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
}
case 1:
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
x_16 = lean_box(x_1);
x_17 = lean_box(x_2);
x_18 = lean_apply_2(x_6, x_16, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(x_2);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
x_22 = lean_box(x_1);
x_23 = lean_box(x_2);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102__match__1___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
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
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqMessageSeverity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102____boxed), 2, 0);
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
lean_object* l_Lean_MessageData_instantiateMVars_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 6:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_3, x_13, x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_4, x_16, x_17);
return x_18;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_2(x_5, x_19, x_20);
return x_21;
}
case 9:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_1(x_6, x_22);
return x_23;
}
case 10:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_2(x_7, x_24, x_25);
return x_26;
}
case 11:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_2(x_8, x_27, x_28);
return x_29;
}
case 12:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_1(x_9, x_30);
return x_31;
}
default: 
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_apply_1(x_10, x_1);
return x_32;
}
}
}
}
lean_object* l_Lean_MessageData_instantiateMVars_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_instantiateMVars_visit_match__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_MessageData_instantiateMVars_visit(x_10, x_1);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_MessageData_instantiateMVars_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_MetavarContext_instantiateMVars(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_MetavarContext_instantiateMVars(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
case 6:
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_MessageData_instantiateMVars_visit(x_13, x_14);
lean_ctor_set(x_1, 1, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_MessageData_instantiateMVars_visit(x_17, x_18);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
case 7:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = l_Lean_MessageData_instantiateMVars_visit(x_22, x_2);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_MessageData_instantiateMVars_visit(x_25, x_2);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
case 8:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = l_Lean_MessageData_instantiateMVars_visit(x_29, x_2);
lean_ctor_set(x_1, 1, x_30);
return x_1;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = l_Lean_MessageData_instantiateMVars_visit(x_32, x_2);
x_34 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
case 9:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = l_Lean_MessageData_instantiateMVars_visit(x_36, x_2);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_MessageData_instantiateMVars_visit(x_38, x_2);
x_40 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
case 10:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_44 = l_Lean_MessageData_instantiateMVars_visit(x_42, x_2);
x_45 = l_Lean_MessageData_instantiateMVars_visit(x_43, x_2);
lean_ctor_set(x_1, 1, x_45);
lean_ctor_set(x_1, 0, x_44);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
lean_inc(x_2);
x_48 = l_Lean_MessageData_instantiateMVars_visit(x_46, x_2);
x_49 = l_Lean_MessageData_instantiateMVars_visit(x_47, x_2);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
case 11:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 1);
x_53 = l_Lean_MessageData_instantiateMVars_visit(x_52, x_2);
lean_ctor_set(x_1, 1, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_1);
x_56 = l_Lean_MessageData_instantiateMVars_visit(x_55, x_2);
x_57 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
case 12:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = 0;
x_63 = x_59;
x_64 = l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1(x_2, x_61, x_62, x_63);
x_65 = x_64;
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_array_get_size(x_66);
x_68 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_69 = 0;
x_70 = x_66;
x_71 = l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1(x_2, x_68, x_69, x_70);
x_72 = x_71;
x_73 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_MessageData_instantiateMVars_visit___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_MessageData_instantiateMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instantiateMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instantiateMVars___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instantiateMVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_instantiateMVars___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instantiateMVars___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MessageData_instantiateMVars___closed__3;
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_instantiateMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_instantiateMVars___closed__4;
x_3 = l_Lean_MessageData_instantiateMVars_visit(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_hasTag_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
case 7:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_3, x_13, x_14);
return x_15;
}
case 8:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_4, x_16, x_17);
return x_18;
}
case 9:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_1(x_5, x_19);
return x_20;
}
case 10:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_2(x_6, x_21, x_22);
return x_23;
}
case 11:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_2(x_7, x_24, x_25);
return x_26;
}
case 12:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_apply_1(x_8, x_27);
return x_28;
}
default: 
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_apply_1(x_9, x_1);
return x_29;
}
}
}
}
lean_object* l_Lean_MessageData_hasTag_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_hasTag_match__1___rarg), 9, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_MessageData_hasTag(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
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
uint8_t l_Lean_MessageData_hasTag(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_2 = x_3;
goto _start;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
case 8:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
case 9:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
case 10:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
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
x_15 = 1;
return x_15;
}
}
case 11:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_name_eq(x_1, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
x_2 = x_17;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_17);
x_20 = 1;
return x_20;
}
}
case 12:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = 0;
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_27 = 0;
return x_27;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(x_1, x_21, x_28, x_29);
lean_dec(x_21);
return x_30;
}
}
}
default: 
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = 0;
return x_31;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasTag___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_hasTag(x_1, x_2);
lean_dec(x_1);
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
lean_object* l_Lean_MessageData_isNil_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
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
lean_object* l_Lean_MessageData_isNil_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_isNil_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_MessageData_isNil(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
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
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_MessageData_isNil___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isNil(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_isNest_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_MessageData_isNest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_isNest_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_MessageData_isNest(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
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
lean_object* l_Lean_MessageData_isNest___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isNest(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_mkPPContext(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_mkPPContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageData_formatAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_apply_3(x_4, x_1, x_2, x_20);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_apply_2(x_8, x_1, x_22);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_apply_2(x_9, x_1, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_apply_3(x_5, x_1, x_2, x_26);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_apply_3(x_6, x_1, x_2, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_apply_2(x_11, x_1, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_apply_4(x_13, x_1, x_2, x_32, x_33);
return x_34;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_apply_4(x_14, x_1, x_2, x_35, x_36);
return x_37;
}
case 8:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_apply_4(x_16, x_1, x_2, x_38, x_39);
return x_40;
}
case 9:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_apply_3(x_18, x_1, x_2, x_41);
return x_42;
}
case 10:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_apply_4(x_17, x_1, x_2, x_43, x_44);
return x_45;
}
case 11:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_apply_4(x_15, x_1, x_2, x_46, x_47);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_apply_3(x_19, x_1, x_2, x_49);
return x_50;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_apply_3(x_4, x_1, x_2, x_51);
return x_52;
}
case 1:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
lean_dec(x_3);
x_55 = lean_apply_3(x_7, x_1, x_53, x_54);
return x_55;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_ctor_get(x_3, 0);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_apply_3(x_10, x_1, x_56, x_57);
return x_58;
}
case 3:
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_apply_3(x_5, x_1, x_2, x_59);
return x_60;
}
case 4:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_apply_3(x_6, x_1, x_2, x_61);
return x_62;
}
case 5:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_ctor_get(x_3, 0);
lean_inc(x_64);
lean_dec(x_3);
x_65 = lean_apply_3(x_12, x_1, x_63, x_64);
return x_65;
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_apply_4(x_13, x_1, x_2, x_66, x_67);
return x_68;
}
case 7:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_ctor_get(x_3, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 1);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_apply_4(x_14, x_1, x_2, x_69, x_70);
return x_71;
}
case 8:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
lean_dec(x_3);
x_74 = lean_apply_4(x_16, x_1, x_2, x_72, x_73);
return x_74;
}
case 9:
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
lean_dec(x_3);
x_76 = lean_apply_3(x_18, x_1, x_2, x_75);
return x_76;
}
case 10:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_inc(x_78);
lean_dec(x_3);
x_79 = lean_apply_4(x_17, x_1, x_2, x_77, x_78);
return x_79;
}
case 11:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = lean_ctor_get(x_3, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
lean_dec(x_3);
x_82 = lean_apply_4(x_15, x_1, x_2, x_80, x_81);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_apply_3(x_19, x_1, x_2, x_83);
return x_84;
}
}
}
}
}
lean_object* l_Lean_MessageData_formatAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_formatAux_match__1___rarg___boxed), 19, 0);
return x_2;
}
}
lean_object* l_Lean_MessageData_formatAux_match__1___rarg___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_Lean_MessageData_formatAux_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 == x_5;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MessageData_formatAux(x_1, x_2, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = 1;
x_17 = x_4 + x_16;
x_4 = x_17;
x_6 = x_15;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
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
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 == x_5;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MessageData_formatAux(x_1, x_2, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = 1;
x_17 = x_4 + x_16;
x_4 = x_17;
x_6 = x_15;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
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
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("goal ");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_formatAux___closed__3;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_formatStxAux(x_8, x_9, x_10, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_expr_dbg_to_string(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_Level_format(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
case 4:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = 1;
x_22 = l_Lean_Name_toString(x_20, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_mkMVar(x_25);
x_27 = lean_expr_dbg_to_string(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_formatAux___closed__2;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_2 = x_34;
x_3 = x_33;
goto _start;
}
case 7:
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_1 = x_36;
x_3 = x_37;
goto _start;
}
case 8:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec(x_3);
x_41 = l_Lean_MessageData_formatAux(x_1, x_2, x_40, x_4);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_nat_to_int(x_39);
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_nat_to_int(x_39);
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_39);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 9:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = l_Lean_MessageData_formatAux(x_1, x_2, x_55, x_4);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = 0;
x_60 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
x_63 = 0;
x_64 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 1);
lean_inc(x_71);
lean_dec(x_3);
lean_inc(x_1);
x_72 = l_Lean_MessageData_formatAux(x_1, x_2, x_70, x_4);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MessageData_formatAux(x_1, x_2, x_71, x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_73);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
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
lean_dec(x_71);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
case 11:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_dec(x_3);
x_3 = x_91;
goto _start;
}
default: 
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
lean_dec(x_3);
x_94 = lean_array_get_size(x_93);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_97 = l_Lean_MessageData_formatAux___closed__4;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_4);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_le(x_94, x_94);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_100 = l_Lean_MessageData_formatAux___closed__4;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_104 = lean_box(0);
x_105 = l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1(x_1, x_2, x_93, x_102, x_103, x_104, x_4);
lean_dec(x_93);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = l_Lean_MessageData_formatAux___closed__3;
x_109 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_105, 0, x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_105);
x_112 = l_Lean_MessageData_formatAux___closed__3;
x_113 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_105);
if (x_115 == 0)
{
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
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
lean_object* x_119; lean_object* x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
lean_dec(x_3);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_4);
return x_120;
}
case 1:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_2, 0);
lean_inc(x_121);
lean_dec(x_2);
x_122 = lean_ctor_get(x_3, 0);
lean_inc(x_122);
lean_dec(x_3);
x_123 = l_Lean_MessageData_mkPPContext(x_1, x_121);
lean_dec(x_121);
lean_dec(x_1);
x_124 = l_Lean_ppTerm(x_123, x_122, x_4);
return x_124;
}
case 2:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_2, 0);
lean_inc(x_125);
lean_dec(x_2);
x_126 = lean_ctor_get(x_3, 0);
lean_inc(x_126);
lean_dec(x_3);
x_127 = l_Lean_MessageData_mkPPContext(x_1, x_125);
lean_dec(x_125);
lean_dec(x_1);
x_128 = l_Lean_ppExpr(x_127, x_126, x_4);
return x_128;
}
case 3:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_3, 0);
lean_inc(x_129);
lean_dec(x_3);
x_130 = l_Lean_Level_format(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_4);
return x_131;
}
case 4:
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_3, 0);
lean_inc(x_132);
lean_dec(x_3);
x_133 = 1;
x_134 = l_Lean_Name_toString(x_132, x_133);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
return x_136;
}
case 5:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
lean_dec(x_2);
x_138 = lean_ctor_get(x_3, 0);
lean_inc(x_138);
lean_dec(x_3);
x_139 = l_Lean_MessageData_mkPPContext(x_1, x_137);
lean_dec(x_137);
lean_dec(x_1);
x_140 = l_Lean_ppGoal(x_139, x_138, x_4);
return x_140;
}
case 6:
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_2);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_2, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_3, 1);
lean_inc(x_144);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_143);
x_3 = x_144;
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_2);
x_146 = lean_ctor_get(x_3, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_3, 1);
lean_inc(x_147);
lean_dec(x_3);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_146);
x_2 = x_148;
x_3 = x_147;
goto _start;
}
}
case 7:
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_1);
x_150 = lean_ctor_get(x_3, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_3, 1);
lean_inc(x_151);
lean_dec(x_3);
x_1 = x_150;
x_3 = x_151;
goto _start;
}
case 8:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_3, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_3, 1);
lean_inc(x_154);
lean_dec(x_3);
x_155 = l_Lean_MessageData_formatAux(x_1, x_2, x_154, x_4);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_nat_to_int(x_153);
x_159 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_155, 0, x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_155, 0);
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_155);
x_162 = lean_nat_to_int(x_153);
x_163 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_153);
x_165 = !lean_is_exclusive(x_155);
if (x_165 == 0)
{
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_155, 0);
x_167 = lean_ctor_get(x_155, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_155);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
case 9:
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_3, 0);
lean_inc(x_169);
lean_dec(x_3);
x_170 = l_Lean_MessageData_formatAux(x_1, x_2, x_169, x_4);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = 0;
x_174 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
lean_ctor_set(x_170, 0, x_174);
return x_170;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_170, 0);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_170);
x_177 = 0;
x_178 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_170);
if (x_180 == 0)
{
return x_170;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_170, 0);
x_182 = lean_ctor_get(x_170, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_170);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
case 10:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_3, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_3, 1);
lean_inc(x_185);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_186 = l_Lean_MessageData_formatAux(x_1, x_2, x_184, x_4);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_MessageData_formatAux(x_1, x_2, x_185, x_188);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_189, 0, x_192);
return x_189;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_189);
x_195 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_195, 0, x_187);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
uint8_t x_197; 
lean_dec(x_187);
x_197 = !lean_is_exclusive(x_189);
if (x_197 == 0)
{
return x_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_189, 0);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_189);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_185);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_186);
if (x_201 == 0)
{
return x_186;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_186, 0);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_186);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 11:
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_3, 1);
lean_inc(x_205);
lean_dec(x_3);
x_3 = x_205;
goto _start;
}
default: 
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_3, 0);
lean_inc(x_207);
lean_dec(x_3);
x_208 = lean_array_get_size(x_207);
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_lt(x_209, x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_2);
lean_dec(x_1);
x_211 = l_Lean_MessageData_formatAux___closed__4;
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_4);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_208, x_208);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_2);
lean_dec(x_1);
x_214 = l_Lean_MessageData_formatAux___closed__4;
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_4);
return x_215;
}
else
{
size_t x_216; size_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = 0;
x_217 = lean_usize_of_nat(x_208);
lean_dec(x_208);
x_218 = lean_box(0);
x_219 = l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2(x_1, x_2, x_207, x_216, x_217, x_218, x_4);
lean_dec(x_207);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = l_Lean_MessageData_formatAux___closed__3;
x_223 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
lean_ctor_set(x_219, 0, x_223);
return x_219;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_219, 0);
x_225 = lean_ctor_get(x_219, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_219);
x_226 = l_Lean_MessageData_formatAux___closed__3;
x_227 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_219);
if (x_229 == 0)
{
return x_219;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_219, 0);
x_231 = lean_ctor_get(x_219, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_219);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__1(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_MessageData_formatAux___spec__2(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
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
lean_object* l_Lean_MessageData_format(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_MessageData_format___closed__1;
x_5 = l_Lean_MessageData_formatAux(x_4, x_3, x_1, x_2);
return x_5;
}
}
lean_object* l_Lean_MessageData_toString(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_MessageData_instAppendMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeStringMessageData___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_MessageData_instCoeFormatMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeLevelMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeExprMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeNameMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeSyntaxMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeOptionExprMessageData_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExprMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeOptionExprMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData(lean_object* x_1) {
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
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
lean_object* l_Lean_MessageData_instCoeOptionExprMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeOptionExprMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_arrayExpr_toMessageData___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_alloc_ctor(10, 2, 0);
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
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_12;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_8);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
}
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string("#[");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExprMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_instCoeArrayExprMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_MessageData_instCoeArrayExprMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MessageData_instCoeArrayExprMessageData___closed__3;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_instCoeArrayExprMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeArrayExprMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_MessageData_paren___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_paren___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_paren___closed__1;
x_3 = l_Lean_MessageData_paren___closed__2;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MessageData_sbracket___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_sbracket___closed__1;
x_3 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_joinSep_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_3(x_5, x_10, x_7, x_2);
return x_11;
}
}
}
}
lean_object* l_Lean_MessageData_joinSep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_joinSep_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_MessageData_joinSep(x_4, x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_MessageData_joinSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageData_ofList_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_MessageData_ofList_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofList_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_ofList(lean_object* x_1) {
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
x_5 = l_Lean_MessageData_sbracket___closed__1;
x_6 = l_Lean_MessageData_arrayExpr_toMessageData___closed__1;
x_7 = l_Lean_MessageData_bracket(x_5, x_4, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MessageData_ofList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofList___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeListMessageDataMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1;
return x_1;
}
}
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_5);
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
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_MessageData_instCoeListExprMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_mkErrorStringWithPos___closed__1;
x_3 = l_Lean_instInhabitedMessage___closed__1;
x_4 = 0;
x_5 = l_Lean_instInhabitedMessageData___closed__1;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
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
lean_object* l_Lean_Message_toString_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Message_toString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Message_toString_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Message_toString_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Message_toString_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Message_toString___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Message_toString___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
lean_object* l_Lean_Message_toString___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Message_toString___lambda__2___closed__2;
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
x_15 = l_Lean_Message_toString___lambda__2___closed__2;
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
x_1 = lean_mk_string("warning: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Message_toString___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error: ");
return x_1;
}
}
lean_object* l_Lean_Message_toString___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Message_toString___lambda__3___closed__1;
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
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
x_1 = lean_mk_string(":\n");
return x_1;
}
}
lean_object* l_Lean_Message_toString(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
lean_object* l_Lean_Message_toString___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Message_toString___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Message_toString___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Message_toString___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Message_toString___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Message_toString___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Message_toString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Lean_MessageLog_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Std_PersistentArray_isEmpty___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_push___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_append___rarg(x_1, x_2);
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
lean_object* l_Lean_MessageLog_hasErrors_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_MessageLog_hasErrors_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageLog_hasErrors_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MessageLog_hasErrors_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_MessageLog_hasErrors_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
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
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
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
x_10 = x_2 + x_9;
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
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(lean_object* x_1) {
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
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3(x_2, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = 0;
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(x_12, x_19, x_20);
lean_dec(x_12);
return x_21;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_2);
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
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4(x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*5);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = lean_box(x_13);
if (lean_obj_tag(x_18) == 2)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_9, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_9, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_9, 0);
lean_dec(x_24);
x_25 = 1;
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_25);
x_26 = x_9;
x_27 = lean_array_uset(x_8, x_2, x_26);
x_2 = x_17;
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_12);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_15);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_29);
x_31 = x_30;
x_32 = lean_array_uset(x_8, x_2, x_31);
x_2 = x_17;
x_3 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = x_9;
x_35 = lean_array_uset(x_8, x_2, x_34);
x_2 = x_17;
x_3 = x_35;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = x_3;
x_8 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(x_5, x_6, x_7);
x_9 = x_8;
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = x_10;
x_15 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3(x_12, x_13, x_14);
x_16 = x_15;
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = x_19;
x_24 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_21, x_22, x_23);
x_25 = x_24;
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = x_26;
x_31 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_28, x_29, x_30);
x_32 = x_31;
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = x_4;
x_10 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_7, x_8, x_9);
x_11 = x_10;
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get_usize(x_1, 4);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_17 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_12);
x_18 = lean_array_get_size(x_13);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = x_13;
x_22 = l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4(x_19, x_20, x_21);
x_23 = x_22;
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set_usize(x_24, 4, x_15);
return x_24;
}
}
}
lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_MessageLog_errorsToWarnings___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_MessageLog_getInfoMessages_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 0)
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
lean_object* l_Lean_MessageLog_getInfoMessages_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageLog_getInfoMessages_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MessageLog_getInfoMessages_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_MessageLog_getInfoMessages_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(x_6, x_4);
x_8 = 1;
x_9 = x_2 + x_8;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
x_8 = 1;
x_9 = x_2 + x_8;
x_10 = lean_box(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Std_PersistentArray_push___rarg(x_4, x_6);
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
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3 % (sizeof(size_t) * 8);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3 % (sizeof(size_t) * 8);
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_9, x_13, x_15, x_4);
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
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_8, x_9, x_10, x_2);
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
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__3(x_27, x_2);
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
lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageLog_msgs___default___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_MessageLog_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_forM___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageLog_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageLog_forM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(x_6, x_4);
x_8 = 1;
x_9 = x_2 + x_8;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = 1;
x_9 = x_2 + x_8;
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
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3 % (sizeof(size_t) * 8);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3 % (sizeof(size_t) * 8);
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_9, x_13, x_15, x_4);
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
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_8, x_9, x_10, x_2);
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
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__3(x_27, x_2);
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
lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2, x_3);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MessageLog_toList___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_toList___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_MessageData_nestD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_MessageData_ofList___closed__7;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_indentExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_indentD(x_2);
return x_3;
}
}
lean_object* l_Lean_instAddMessageContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_instAddMessageContext(lean_object* x_1, lean_object* x_2) {
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
x_1 = l_Lean_MessageData_instantiateMVars___closed__3;
x_2 = l_Lean_MessageLog_msgs___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_MessageData_instantiateMVars___closed__4;
x_8 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_4);
x_10 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_addMessageContextPartial___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_addMessageContextPartial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_addMessageContextFull___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_addMessageContextFull___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_addMessageContextFull___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_addMessageContextFull___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_addMessageContextFull___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_addMessageContextFull(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg), 6, 0);
return x_2;
}
}
lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 10;
x_8 = x_6 == x_7;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
x_14 = lean_string_utf8_extract(x_1, x_2, x_13);
lean_dec(x_13);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_List_reverse___rarg(x_18);
return x_19;
}
}
}
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_Lean_stringToMessageData___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
lean_object* l_List_map___at_Lean_stringToMessageData___spec__3(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___at_Lean_stringToMessageData___spec__3(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___at_Lean_stringToMessageData___spec__3(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_stringToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_split___at_Lean_stringToMessageData___spec__1(x_1);
x_3 = l_List_map___at_Lean_stringToMessageData___spec__3(x_2);
x_4 = l_Lean_MessageData_ofList___closed__7;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_String_splitAux___at_Lean_stringToMessageData___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_Lean_stringToMessageData___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_Lean_stringToMessageData___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_stringToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_instToMessageData___rarg(lean_object* x_1) {
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
lean_object* l_Lean_instToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageData___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* l_Lean_instToMessageDataSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
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
lean_object* l_Lean_instToMessageDataList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_map___rarg(x_1, x_2);
x_4 = l_Lean_MessageData_ofList(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_instToMessageDataList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = l_List_map___rarg(x_1, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_instToMessageDataArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_instToMessageDataOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_instToMessageDataOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some (");
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOption___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_instToMessageDataOption___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_instToMessageDataOption___rarg___closed__5;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_instToMessageDataOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<not-available>");
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToMessageDataOptionExpr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* l_Lean_instToMessageDataOptionExpr(lean_object* x_1) {
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
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
lean_object* l_Lean_instToMessageDataOptionExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToMessageDataOptionExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termM!_");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__2;
x_2 = l_Lean_termM_x21_____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("m!");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termM_x21_____closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interpolatedStr");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_termM_x21_____closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__10;
x_2 = l_Lean_termM_x21_____closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termM_x21_____closed__6;
x_2 = l_Lean_termM_x21_____closed__8;
x_3 = l_Lean_termM_x21_____closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termM_x21_____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termM_x21_____closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_termM_x21_____closed__15;
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
x_1 = l_Lean_termM_x21_____closed__16;
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__2;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toMessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ToMessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termM_x21_____closed__2;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_2313_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termM_x21_____closed__4;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_2);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_72____spec__1(x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4;
lean_inc(x_13);
lean_inc(x_14);
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3;
x_18 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7;
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
lean_inc(x_2);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_72____spec__1(x_2, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11;
x_24 = l_Lean_addMacroScope(x_14, x_23, x_13);
x_25 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10;
x_26 = l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_Syntax_expandInterpolatedStr(x_9, x_19, x_27, x_2, x_22);
lean_dec(x_9);
return x_28;
}
}
}
lean_object* l___private_Lean_Message_0__Lean_KernelException_mkCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_MessageData_instantiateMVars___closed__4;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
x_7 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
lean_object* l_Lean_KernelException_toMessageData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(x_9);
x_14 = lean_apply_6(x_2, x_10, x_12, x_11, x_7, x_8, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
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
x_21 = lean_apply_4(x_3, x_18, x_20, x_19, x_17);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_1(x_4, x_1);
return x_22;
}
}
}
}
lean_object* l_Lean_KernelException_toMessageData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_KernelException_toMessageData_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_KernelException_toMessageData_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_2, x_14, x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_2(x_3, x_17, x_18);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_3(x_4, x_20, x_21, x_22);
return x_23;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_3(x_5, x_24, x_25, x_26);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_3(x_6, x_28, x_29, x_30);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_apply_3(x_7, x_32, x_33, x_34);
return x_35;
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_apply_3(x_8, x_36, x_37, x_38);
return x_39;
}
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_apply_5(x_9, x_40, x_41, x_42, x_43, x_44);
return x_45;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_apply_4(x_10, x_46, x_47, x_48, x_49);
return x_50;
}
case 9:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 4);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_apply_5(x_11, x_51, x_52, x_53, x_54, x_55);
return x_56;
}
case 10:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
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
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_apply_3(x_12, x_57, x_58, x_59);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
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
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_apply_1(x_13, x_61);
return x_62;
}
}
}
}
lean_object* l_Lean_KernelException_toMessageData_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_KernelException_toMessageData_match__2___rarg), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) unknown constant '");
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
x_1 = lean_mk_string("'");
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
x_1 = lean_mk_string("(kernel) constant has already been declared '");
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
x_1 = lean_mk_string("(kernel) declaration type mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_1 = lean_mk_string("(kernel) declaration type mismatch, '");
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
x_1 = lean_mk_string("' has type");
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
x_1 = lean_mk_string("\nbut it is expected to have type");
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
x_1 = lean_mk_string("(kernel) declaration has metavariables '");
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
x_1 = lean_mk_string("(kernel) declaration has free variables '");
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
x_1 = lean_mk_string("(kernel) function expected");
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
x_1 = lean_mk_string("(kernel) type expected");
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
x_1 = lean_mk_string("(kernel) let-declaration type mismatch '");
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
x_1 = lean_mk_string("(kernel) type mismatch at");
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
x_1 = lean_mk_string("application type mismatch");
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
x_1 = lean_mk_string("\nargument has type");
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
x_1 = lean_mk_string("\nbut function has type");
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
x_1 = lean_mk_string("(kernel) invalid projection");
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
x_1 = lean_mk_string("(kernel) ");
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
lean_object* l_Lean_KernelException_toMessageData(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_KernelException_toMessageData___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_KernelException_toMessageData___closed__4;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
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
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_KernelException_toMessageData___closed__6;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_KernelException_toMessageData___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
x_20 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_12, x_19, x_2, x_18);
return x_20;
}
case 2:
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_KernelException_toMessageData___closed__11;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_KernelException_toMessageData___closed__13;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_24);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_KernelException_toMessageData___closed__15;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_indentExpr(x_26);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_KernelException_toMessageData___closed__16;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = l_Lean_KernelException_toMessageData___closed__11;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_KernelException_toMessageData___closed__13;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_indentExpr(x_42);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_KernelException_toMessageData___closed__15;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_44);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_KernelException_toMessageData___closed__16;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
default: 
{
lean_object* x_58; 
lean_dec(x_21);
lean_dec(x_1);
x_58 = l_Lean_KernelException_toMessageData___closed__9;
return x_58;
}
}
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_KernelException_toMessageData___closed__18;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_KernelException_toMessageData___closed__4;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
x_67 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_59, x_66, x_2, x_65);
return x_67;
}
case 4:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_KernelException_toMessageData___closed__20;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_KernelException_toMessageData___closed__4;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1;
x_76 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_68, x_75, x_2, x_74);
return x_76;
}
case 5:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
lean_dec(x_1);
x_80 = l_Lean_indentExpr(x_79);
x_81 = l_Lean_KernelException_toMessageData___closed__22;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_KernelException_toMessageData___closed__16;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_77, x_78, x_2, x_84);
return x_85;
}
case 6:
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
x_90 = l_Lean_KernelException_toMessageData___closed__24;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_KernelException_toMessageData___closed__16;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_86, x_87, x_2, x_93);
return x_94;
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 2);
lean_inc(x_97);
lean_dec(x_1);
x_98 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_KernelException_toMessageData___closed__26;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_KernelException_toMessageData___closed__4;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_95, x_96, x_2, x_102);
return x_103;
}
case 8:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_indentExpr(x_106);
x_108 = l_Lean_KernelException_toMessageData___closed__28;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_KernelException_toMessageData___closed__16;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_104, x_105, x_2, x_111);
return x_112;
}
case 9:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 4);
lean_inc(x_117);
lean_dec(x_1);
x_118 = l_Lean_indentExpr(x_115);
x_119 = l_Lean_KernelException_toMessageData___closed__30;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_KernelException_toMessageData___closed__32;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_indentExpr(x_117);
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_KernelException_toMessageData___closed__34;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_indentExpr(x_116);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_KernelException_toMessageData___closed__16;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_113, x_114, x_2, x_130);
return x_131;
}
case 10:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_1, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 2);
lean_inc(x_134);
lean_dec(x_1);
x_135 = l_Lean_indentExpr(x_134);
x_136 = l_Lean_KernelException_toMessageData___closed__36;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_KernelException_toMessageData___closed__16;
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Lean_Message_0__Lean_KernelException_mkCtx(x_132, x_133, x_2, x_139);
return x_140;
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
lean_dec(x_1);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = l_Lean_KernelException_toMessageData___closed__38;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_KernelException_toMessageData___closed__16;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Position(lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Util_PPExt(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Message(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(lean_io_mk_world());
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
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instBEqMessageSeverity___closed__1 = _init_l_Lean_instBEqMessageSeverity___closed__1();
lean_mark_persistent(l_Lean_instBEqMessageSeverity___closed__1);
l_Lean_instBEqMessageSeverity = _init_l_Lean_instBEqMessageSeverity();
lean_mark_persistent(l_Lean_instBEqMessageSeverity);
l_Lean_instInhabitedMessageData___closed__1 = _init_l_Lean_instInhabitedMessageData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedMessageData___closed__1);
l_Lean_instInhabitedMessageData = _init_l_Lean_instInhabitedMessageData();
lean_mark_persistent(l_Lean_instInhabitedMessageData);
l_Lean_MessageData_instantiateMVars___closed__1 = _init_l_Lean_MessageData_instantiateMVars___closed__1();
lean_mark_persistent(l_Lean_MessageData_instantiateMVars___closed__1);
l_Lean_MessageData_instantiateMVars___closed__2 = _init_l_Lean_MessageData_instantiateMVars___closed__2();
lean_mark_persistent(l_Lean_MessageData_instantiateMVars___closed__2);
l_Lean_MessageData_instantiateMVars___closed__3 = _init_l_Lean_MessageData_instantiateMVars___closed__3();
lean_mark_persistent(l_Lean_MessageData_instantiateMVars___closed__3);
l_Lean_MessageData_instantiateMVars___closed__4 = _init_l_Lean_MessageData_instantiateMVars___closed__4();
lean_mark_persistent(l_Lean_MessageData_instantiateMVars___closed__4);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
l_Lean_MessageData_formatAux___closed__1 = _init_l_Lean_MessageData_formatAux___closed__1();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__1);
l_Lean_MessageData_formatAux___closed__2 = _init_l_Lean_MessageData_formatAux___closed__2();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__2);
l_Lean_MessageData_formatAux___closed__3 = _init_l_Lean_MessageData_formatAux___closed__3();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__3);
l_Lean_MessageData_formatAux___closed__4 = _init_l_Lean_MessageData_formatAux___closed__4();
lean_mark_persistent(l_Lean_MessageData_formatAux___closed__4);
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
l_Lean_MessageData_sbracket___closed__1 = _init_l_Lean_MessageData_sbracket___closed__1();
lean_mark_persistent(l_Lean_MessageData_sbracket___closed__1);
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
l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1 = _init_l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1();
lean_mark_persistent(l_Lean_MessageData_instCoeListMessageDataMessageData___closed__1);
l_Lean_MessageData_instCoeListMessageDataMessageData = _init_l_Lean_MessageData_instCoeListMessageDataMessageData();
lean_mark_persistent(l_Lean_MessageData_instCoeListMessageDataMessageData);
l_Lean_Message_endPos___default = _init_l_Lean_Message_endPos___default();
lean_mark_persistent(l_Lean_Message_endPos___default);
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
l_Lean_Message_toString___lambda__2___closed__2 = _init_l_Lean_Message_toString___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Message_toString___lambda__2___closed__2);
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
l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1 = _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1();
lean_mark_persistent(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_MessageLog_getInfoMessages___spec__2___closed__1);
l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1 = _init_l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___rarg___lambda__1___closed__1);
l_Lean_instToMessageDataString___closed__1 = _init_l_Lean_instToMessageDataString___closed__1();
lean_mark_persistent(l_Lean_instToMessageDataString___closed__1);
l_Lean_instToMessageDataString = _init_l_Lean_instToMessageDataString();
lean_mark_persistent(l_Lean_instToMessageDataString);
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
l_Lean_termM_x21_____closed__16 = _init_l_Lean_termM_x21_____closed__16();
lean_mark_persistent(l_Lean_termM_x21_____closed__16);
l_Lean_termM_x21__ = _init_l_Lean_termM_x21__();
lean_mark_persistent(l_Lean_termM_x21__);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__1);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__2);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__3);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__4);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__5);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__6);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__7);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__8);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__9);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__10);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__11);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__12);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__13);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__14);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__15);
l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_2313____closed__16);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
