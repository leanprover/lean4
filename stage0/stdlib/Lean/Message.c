// Lean compiler output
// Module: Lean.Message
// Imports: Init Lean.Data.Position Lean.Data.OpenDecl Lean.Syntax Lean.MetavarContext Lean.Environment Lean.Util.PPExt Lean.Util.PPGoal
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
lean_object* l_Lean_KernelException_toMessageData___closed__32;
lean_object* l_Lean_KernelException_toMessageData___closed__10;
extern lean_object* l_Lean_toStringToFormat___rarg___closed__1;
lean_object* l_Lean_Lean_Message___instance__1(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__51;
lean_object* l_Lean_addMessageContextPartial___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_MessageData_isNest(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__19;
extern lean_object* l_addParenHeuristic___closed__2;
lean_object* l_Lean_KernelException_toMessageData___closed__49;
lean_object* l_Lean_Lean_Message___instance__3(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__11___rarg___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Lean_Message___instance__11_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5;
lean_object* l_Lean_KernelException_toMessageData___closed__7;
lean_object* l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray___boxed(lean_object*);
lean_object* l_Lean_Message_toString___closed__3;
lean_object* l_Lean_MessageLog_Inhabited;
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l_Lean_Lean_Message___instance__11___rarg___closed__1;
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2;
lean_object* l_Lean_MessageData_hasCoeOfName(lean_object*);
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
lean_object* l_Lean_Lean_Message___instance__9(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7;
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__24;
lean_object* l_Lean_MessageData_sbracket(lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__10___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfSyntax(lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
lean_object* l_List_map___main___at_Lean_stringToMessageData___spec__4(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_MessageData_coeOfLevel(lean_object*);
lean_object* l_Lean_Lean_Message___instance__9___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfList;
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_MessageData_hasCoeOfExpr(lean_object*);
lean_object* l_Lean_MessageData_coeOfFormat(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__43;
lean_object* l_Lean_Lean_Message___instance__11___rarg___closed__2;
lean_object* l_Lean_Lean_Message___instance__12(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitAux___main___at_Lean_stringToMessageData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__16;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l_Lean_MessageData_coeOfString;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Lean_Message___instance__12___closed__3;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
lean_object* l_Lean_Lean_Message___instance__10___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfOptExpr___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6;
lean_object* l_Lean_KernelException_toMessageData___closed__20;
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_Lean_Lean_Message___instance__7(lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__22;
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__37;
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3;
lean_object* lean_message_string(lean_object*);
lean_object* l_Lean_MessageData_coeOfList;
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
extern lean_object* l_EStateM_Result_toString___rarg___closed__2;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_MessageLog_toList(lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5;
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3;
lean_object* l_Lean_KernelException_toMessageData___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__46;
lean_object* l_Lean_Lean_Message___instance__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__1;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfName(lean_object*);
lean_object* l_Lean_MessageData_coeOfOptExpr(lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
lean_object* l_Lean_MessageData_hasCoeOfList___closed__1;
lean_object* l_Lean_Lean_Message___instance__11_match__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__6(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Lean_Lean_Message___instance__11___rarg___closed__3;
lean_object* l_Lean_KernelException_toMessageData___closed__29;
lean_object* l_Lean_fmt___at_Lean_MessageData_formatAux___main___spec__1(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4;
lean_object* l_Lean_stringToMessageData___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfListExpr(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
extern lean_object* l_stdNext___closed__1;
uint8_t l_Lean_MessageData_isNil(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__25;
lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__30;
lean_object* l_Lean_Message_Inhabited;
lean_object* l_Lean_MessageLog_HasAppend;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__18;
lean_object* l_Lean_MessageData_hasCoeOfOptExpr___closed__1;
lean_object* l_Lean_Message_toString___closed__4;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
lean_object* l_Lean_KernelException_toMessageData___closed__5;
lean_object* l_Lean_Lean_Message___instance__1___rarg(lean_object*);
lean_object* l_Lean_MessageData_nil___closed__1;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8;
lean_object* l_Lean_KernelException_toMessageData___closed__33;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_KernelException_toMessageData___closed__14;
lean_object* l_Lean_KernelException_toMessageData___closed__28;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__1;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9;
lean_object* l_Lean_Message_toString___closed__2;
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10;
lean_object* l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_addMessageContextTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5;
lean_object* l_Lean_KernelException_toMessageData___closed__34;
lean_object* l_Lean_MessageData_coeOfArrayExpr(lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___closed__1;
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main___closed__1;
lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__42;
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_getInfoMessages___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__2;
lean_object* l_Lean_KernelException_toMessageData___closed__27;
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
lean_object* l_Lean_MessageData_ofList___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__40;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__9;
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Message_1__mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfLevel(lean_object*);
lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__36;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_message_severity(lean_object*);
lean_object* l_Lean_Message_getMessageStringEx___closed__1;
lean_object* l_Lean_KernelException_toMessageData___closed__45;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Lean_Message___instance__11___rarg(lean_object*);
lean_object* l_Lean_MessageData_format___closed__1;
lean_object* l_Lean_MessageLog_HasAppend___closed__1;
lean_object* l_Lean_MessageData_ofArray(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2;
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___boxed(lean_object*);
lean_object* l_Lean_MessageLog_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__1;
lean_object* l_Lean_fmt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__11(lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3;
lean_object* l_Lean_Lean_Message___instance__12_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main___closed__2;
lean_object* l_Lean_KernelException_toMessageData___closed__50;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__8;
lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_KernelException_toMessageData___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__11___boxed(lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4;
lean_object* l_Lean_MessageData_nestD(lean_object*);
lean_object* l_Lean_Lean_Message___instance__8;
lean_object* l_Lean_KernelException_toMessageData___closed__17;
lean_object* l_Lean_Lean_Message___instance__2(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__38;
lean_object* l_Lean_KernelException_toMessageData___closed__21;
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__47;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Lean_Message___instance__12___boxed(lean_object*);
lean_object* l_Lean_Lean_Message___instance__12___closed__1;
lean_object* l_Lean_MessageData_coeOfString___lambda__1(lean_object*);
lean_object* l_Lean_MessageLog_getInfoMessages___lambda__1___boxed(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6;
lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
lean_object* l_Std_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_HasAppend(lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_Lean_Message___instance__12___closed__2;
lean_object* l_Lean_KernelException_toMessageData___closed__2;
lean_object* l_Lean_MessageData_ofList___closed__4;
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1;
lean_object* l_Lean_mkMessageEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Message___instance__12_match__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__31;
lean_object* l_Lean_KernelException_toMessageData___closed__35;
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__41;
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextTrans(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_isNest___boxed(lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__23;
lean_object* l_Lean_Lean_Message___instance__10(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__48;
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1;
lean_object* l_Lean_MessageData_hasCoeOfFormat(lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_String_splitAux___main___at_Lean_stringToMessageData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData___closed__13;
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_MessageLog_forM(lean_object*);
lean_object* l_Lean_MessageData_coeOfListExpr(lean_object*);
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6;
lean_object* l_Lean_Message_Inhabited___closed__1;
lean_object* l_Lean_Message_Inhabited___closed__2;
lean_object* l_Lean_MessageData_coeOfOptExpr___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_addMessageContextFull___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object*);
lean_object* l_Lean_MessageData_coeOfString___closed__1;
lean_object* l_Lean_Lean_Message___instance__4(lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Lean_Message___instance__5___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_KernelException_toMessageData___closed__44;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__5;
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__5;
lean_object* lean_message_pos(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__1;
uint8_t l_Lean_MessageLog_isEmpty(lean_object*);
lean_object* l_Lean_MessageData_coeOfExpr(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
lean_object* l_Lean_KernelException_toMessageData___closed__26;
lean_object* l_Lean_Message_getSeverityEx___boxed(lean_object*);
lean_object* l_Lean_MessageLog_append___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__18;
lean_object* l_Lean_MessageData_hasCoeOfSyntax(lean_object*);
uint8_t l_Lean_MessageLog_getInfoMessages___lambda__1(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9;
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_MessageData_hasCoeOfOptExpr(lean_object*);
lean_object* l_Lean_MessageData_coeOfString___closed__2;
extern lean_object* l_Lean_Name_hasMacroScopes___main___closed__1;
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial(lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_MessageData_isNil___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__1;
lean_object* l_Lean_KernelException_toMessageData___closed__11;
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___boxed(lean_object*);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1___boxed(lean_object*);
lean_object* lean_mk_message(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_stringToMessageData___spec__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_getInfoMessages___boxed(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_125_;
lean_object* l_Lean_KernelException_toMessageData___closed__39;
lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_6 = lean_string_append(x_1, x_5);
x_7 = l_Nat_repr(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_5);
x_10 = l_Nat_repr(x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l___private_Init_Util_1__mkPanicMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_4);
return x_14;
}
}
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_nil() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_nil___closed__1;
return x_1;
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
static lean_object* _init_l_Lean_MessageData_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_nil___closed__1;
return x_1;
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
lean_object* l_Lean_fmt___at_Lean_MessageData_formatAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_format(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_4, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_11, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
x_5 = x_13;
x_6 = x_19;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_4, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_11, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
x_5 = x_13;
x_6 = x_19;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("goal ");
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_formatAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_formatAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_mkMVar(x_23);
x_25 = lean_expr_dbg_to_string(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_formatAux___main___closed__2;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
x_2 = x_32;
x_3 = x_31;
goto _start;
}
case 7:
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_1 = x_34;
x_3 = x_35;
goto _start;
}
case 8:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_38, x_4);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_nat_to_int(x_37);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_nat_to_int(x_37);
x_47 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_37);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 9:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
lean_dec(x_3);
x_54 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_53, x_4);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = 0;
x_58 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = 0;
x_62 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 10:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
lean_dec(x_3);
lean_inc(x_1);
x_70 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_68, x_4);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_69, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_71);
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
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
lean_dec(x_69);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_70);
if (x_85 == 0)
{
return x_70;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_70, 0);
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_70);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 11:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_90, x_4);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = l_System_FilePath_dirName___closed__1;
x_95 = l_Lean_Name_toStringWithSep___main(x_94, x_89);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_Format_sbracket___closed__3;
x_98 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Format_sbracket___closed__4;
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Format_sbracket___closed__2;
x_102 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = 0;
x_104 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_106 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_93);
lean_ctor_set(x_91, 0, x_107);
return x_91;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_108 = lean_ctor_get(x_91, 0);
x_109 = lean_ctor_get(x_91, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_91);
x_110 = l_System_FilePath_dirName___closed__1;
x_111 = l_Lean_Name_toStringWithSep___main(x_110, x_89);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_Format_sbracket___closed__3;
x_114 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_Format_sbracket___closed__4;
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Format_sbracket___closed__2;
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = 0;
x_120 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_122 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_109);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_89);
x_125 = !lean_is_exclusive(x_91);
if (x_125 == 0)
{
return x_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_91, 0);
x_127 = lean_ctor_get(x_91, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_91);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_3, 0);
lean_inc(x_129);
lean_dec(x_3);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_box(0);
x_132 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(x_1, x_2, x_129, x_129, x_130, x_131, x_4);
lean_dec(x_129);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = l_stdNext___closed__1;
x_136 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_132, 0, x_136);
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = l_stdNext___closed__1;
x_140 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_132);
if (x_142 == 0)
{
return x_132;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_132, 0);
x_144 = lean_ctor_get(x_132, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_132);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
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
lean_object* x_146; lean_object* x_147; 
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_3, 0);
lean_inc(x_146);
lean_dec(x_3);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_4);
return x_147;
}
case 1:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
lean_dec(x_2);
x_149 = lean_ctor_get(x_3, 0);
lean_inc(x_149);
lean_dec(x_3);
x_150 = l_Lean_MessageData_mkPPContext(x_1, x_148);
lean_dec(x_148);
lean_dec(x_1);
x_151 = l_Lean_ppTerm(x_150, x_149, x_4);
return x_151;
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
lean_dec(x_2);
x_153 = lean_ctor_get(x_3, 0);
lean_inc(x_153);
lean_dec(x_3);
x_154 = l_Lean_MessageData_mkPPContext(x_1, x_152);
lean_dec(x_152);
lean_dec(x_1);
x_155 = l_Lean_ppExpr(x_154, x_153, x_4);
return x_155;
}
case 3:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_3, 0);
lean_inc(x_156);
lean_dec(x_3);
x_157 = l_Lean_Level_format(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_4);
return x_158;
}
case 4:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_3, 0);
lean_inc(x_159);
lean_dec(x_3);
x_160 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_4);
return x_161;
}
case 5:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_2, 0);
lean_inc(x_162);
lean_dec(x_2);
x_163 = lean_ctor_get(x_3, 0);
lean_inc(x_163);
lean_dec(x_3);
x_164 = l_Lean_MessageData_mkPPContext(x_1, x_162);
lean_dec(x_162);
lean_dec(x_1);
x_165 = l_Lean_ppGoal(x_164, x_163, x_4);
return x_165;
}
case 6:
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_2);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_2, 0);
lean_dec(x_167);
x_168 = lean_ctor_get(x_3, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_3, 1);
lean_inc(x_169);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_168);
x_3 = x_169;
goto _start;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_2);
x_171 = lean_ctor_get(x_3, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_3, 1);
lean_inc(x_172);
lean_dec(x_3);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_171);
x_2 = x_173;
x_3 = x_172;
goto _start;
}
}
case 7:
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_1);
x_175 = lean_ctor_get(x_3, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
lean_dec(x_3);
x_1 = x_175;
x_3 = x_176;
goto _start;
}
case 8:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_3, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_3, 1);
lean_inc(x_179);
lean_dec(x_3);
x_180 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_179, x_4);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_nat_to_int(x_178);
x_184 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_180, 0);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_180);
x_187 = lean_nat_to_int(x_178);
x_188 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_178);
x_190 = !lean_is_exclusive(x_180);
if (x_190 == 0)
{
return x_180;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_180, 0);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_180);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
case 9:
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_3, 0);
lean_inc(x_194);
lean_dec(x_3);
x_195 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_194, x_4);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = 0;
x_199 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
lean_ctor_set(x_195, 0, x_199);
return x_195;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_195, 0);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_195);
x_202 = 0;
x_203 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_195);
if (x_205 == 0)
{
return x_195;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_195, 0);
x_207 = lean_ctor_get(x_195, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_195);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
case 10:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_3, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_3, 1);
lean_inc(x_210);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_211 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_209, x_4);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_210, x_213);
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_214, 0, x_217);
return x_214;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_214, 0);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_214);
x_220 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_220, 0, x_212);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
uint8_t x_222; 
lean_dec(x_212);
x_222 = !lean_is_exclusive(x_214);
if (x_222 == 0)
{
return x_214;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_214, 0);
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_214);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_210);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_211);
if (x_226 == 0)
{
return x_211;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_211, 0);
x_228 = lean_ctor_get(x_211, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_211);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
case 11:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_3, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_3, 1);
lean_inc(x_231);
lean_dec(x_3);
x_232 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_231, x_4);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = l_System_FilePath_dirName___closed__1;
x_236 = l_Lean_Name_toStringWithSep___main(x_235, x_230);
x_237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = l_Lean_Format_sbracket___closed__3;
x_239 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
x_240 = l_Lean_Format_sbracket___closed__4;
x_241 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_Format_sbracket___closed__2;
x_243 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = 0;
x_245 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_244);
x_246 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_247 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_234);
lean_ctor_set(x_232, 0, x_248);
return x_232;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_249 = lean_ctor_get(x_232, 0);
x_250 = lean_ctor_get(x_232, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_232);
x_251 = l_System_FilePath_dirName___closed__1;
x_252 = l_Lean_Name_toStringWithSep___main(x_251, x_230);
x_253 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_253, 0, x_252);
x_254 = l_Lean_Format_sbracket___closed__3;
x_255 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = l_Lean_Format_sbracket___closed__4;
x_257 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_Format_sbracket___closed__2;
x_259 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = 0;
x_261 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_260);
x_262 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_263 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_249);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_250);
return x_265;
}
}
else
{
uint8_t x_266; 
lean_dec(x_230);
x_266 = !lean_is_exclusive(x_232);
if (x_266 == 0)
{
return x_232;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_232, 0);
x_268 = lean_ctor_get(x_232, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_232);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
default: 
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = lean_ctor_get(x_3, 0);
lean_inc(x_270);
lean_dec(x_3);
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_box(0);
x_273 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_2, x_270, x_270, x_271, x_272, x_4);
lean_dec(x_270);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = l_stdNext___closed__1;
x_277 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
lean_ctor_set(x_273, 0, x_277);
return x_273;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_273, 0);
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_273);
x_280 = l_stdNext___closed__1;
x_281 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_278);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
}
else
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_273);
if (x_283 == 0)
{
return x_273;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_273, 0);
x_285 = lean_ctor_get(x_273, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_273);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_formatAux___main(x_1, x_2, x_3, x_4);
return x_5;
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
x_5 = l_Lean_MessageData_formatAux___main(x_4, x_3, x_1, x_2);
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
x_6 = lean_box(0);
x_7 = l_Lean_Format_pretty(x_5, x_6);
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
x_10 = lean_box(0);
x_11 = l_Lean_Format_pretty(x_8, x_10);
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
lean_object* l_Lean_MessageData_HasAppend(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_hasCoeOfFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_hasCoeOfOptExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_format___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfOptExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_hasCoeOfOptExpr___closed__1;
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
lean_object* l_Lean_MessageData_hasCoeOfOptExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_hasCoeOfOptExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfString___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_coeOfString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_coeOfString___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_coeOfString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_coeOfString___closed__1;
x_2 = l_Lean_toStringToFormat___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_coeOfString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_coeOfString___closed__2;
return x_1;
}
}
lean_object* l_Lean_MessageData_coeOfFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfOptExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_hasCoeOfOptExpr___closed__1;
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
lean_object* l_Lean_MessageData_coeOfOptExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_coeOfOptExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_sbracket___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatKVMap___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
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
x_13 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
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
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
return x_4;
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
static lean_object* _init_l_Lean_MessageData_hasCoeOfArrayExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_hasCoeOfArrayExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_hasCoeOfArrayExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfArrayExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_coeOfArrayExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_coeOfArrayExpr(x_1);
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
lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Prod_HasRepr___rarg___closed__1;
x_3 = l_ULift_HasRepr___rarg___closed__2;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_repr___rarg___closed__2;
x_3 = l_List_repr___rarg___closed__3;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_joinSep___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = l_Lean_MessageData_nil___closed__1;
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
x_8 = l_Lean_MessageData_joinSep___main(x_4, x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_MessageData_joinSep___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep___main(x_1, x_2);
return x_3;
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
static lean_object* _init_l_Lean_MessageData_ofList___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_ofList___closed__2;
x_2 = l_Lean_MessageData_ofList___closed__3;
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
x_2 = l_Lean_MessageData_ofList___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_MessageData_ofList___closed__4;
x_4 = l_Lean_MessageData_joinSep___main(x_1, x_3);
x_5 = l_List_repr___rarg___closed__2;
x_6 = l_List_repr___rarg___closed__3;
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
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_ofArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_hasCoeOfList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofList___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_hasCoeOfList() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_hasCoeOfList___closed__1;
return x_1;
}
}
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_5);
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
x_11 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_MessageData_hasCoeOfListExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_coeOfList() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_hasCoeOfList___closed__1;
return x_1;
}
}
lean_object* l_Lean_MessageData_coeOfListExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* lean_mk_message(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_4);
return x_9;
}
}
lean_object* l_Lean_mkMessageEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = lean_mk_message(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
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
static lean_object* _init_l_Lean_Message_toString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_string_append(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Message_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("warning: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Message_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Message_toString___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Message_toString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_EStateM_Result_toString___rarg___closed__2;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Message_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = l_Lean_MessageData_toString(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
switch (x_11) {
case 0:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Message_toString___closed__1;
x_16 = lean_string_append(x_12, x_15);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_6);
lean_dec(x_6);
x_19 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_18);
lean_dec(x_18);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_20 = l_Lean_Message_toString___closed__2;
x_21 = lean_string_append(x_20, x_6);
lean_dec(x_6);
x_22 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_21);
lean_dec(x_21);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
}
case 1:
{
if (x_14 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Message_toString___closed__1;
x_24 = lean_string_append(x_12, x_23);
x_25 = l_Lean_Message_toString___closed__3;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = lean_string_append(x_26, x_6);
lean_dec(x_6);
x_28 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_27);
lean_dec(x_27);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_29 = l_Lean_Message_toString___closed__4;
x_30 = lean_string_append(x_29, x_6);
lean_dec(x_6);
x_31 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_30);
lean_dec(x_30);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
}
default: 
{
if (x_14 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = l_Lean_Message_toString___closed__1;
x_33 = lean_string_append(x_12, x_32);
x_34 = l_EStateM_Result_toString___rarg___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_string_append(x_35, x_6);
lean_dec(x_6);
x_37 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_36);
lean_dec(x_36);
lean_ctor_set(x_4, 0, x_37);
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_38 = l_Lean_Message_toString___closed__5;
x_39 = lean_string_append(x_38, x_6);
lean_dec(x_6);
x_40 = l_Lean_mkErrorStringWithPos(x_7, x_9, x_10, x_39);
lean_dec(x_39);
lean_ctor_set(x_4, 0, x_40);
return x_4;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_String_splitAux___main___closed__1;
x_50 = lean_string_dec_eq(x_48, x_49);
switch (x_47) {
case 0:
{
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = l_Lean_Message_toString___closed__1;
x_52 = lean_string_append(x_48, x_51);
x_53 = lean_string_append(x_49, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_53, x_41);
lean_dec(x_41);
x_55 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_48);
x_57 = l_Lean_Message_toString___closed__2;
x_58 = lean_string_append(x_57, x_41);
lean_dec(x_41);
x_59 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
return x_60;
}
}
case 1:
{
if (x_50 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = l_Lean_Message_toString___closed__1;
x_62 = lean_string_append(x_48, x_61);
x_63 = l_Lean_Message_toString___closed__3;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = lean_string_append(x_64, x_41);
lean_dec(x_41);
x_66 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_42);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_48);
x_68 = l_Lean_Message_toString___closed__4;
x_69 = lean_string_append(x_68, x_41);
lean_dec(x_41);
x_70 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
default: 
{
if (x_50 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = l_Lean_Message_toString___closed__1;
x_73 = lean_string_append(x_48, x_72);
x_74 = l_EStateM_Result_toString___rarg___closed__2;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = lean_string_append(x_75, x_41);
lean_dec(x_41);
x_77 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_42);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_48);
x_79 = l_Lean_Message_toString___closed__5;
x_80 = lean_string_append(x_79, x_41);
lean_dec(x_41);
x_81 = l_Lean_mkErrorStringWithPos(x_43, x_45, x_46, x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_42);
return x_82;
}
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_4);
if (x_83 == 0)
{
return x_4;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_4, 0);
x_85 = lean_ctor_get(x_4, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_4);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
static lean_object* _init_l_Lean_Message_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Message_Inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Message_Inhabited___closed__1;
x_4 = 2;
x_5 = l_Lean_MessageData_nil___closed__1;
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
static lean_object* _init_l_Lean_Message_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Message_Inhabited___closed__2;
return x_1;
}
}
lean_object* lean_message_pos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
return x_2;
}
}
uint8_t lean_message_severity(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Message_getSeverityEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_message_severity(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Message_getMessageStringEx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error formatting message: ");
return x_1;
}
}
lean_object* lean_message_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_MessageData_toString(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_2 = x_13;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_2 = x_15;
goto block_8;
}
block_8:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_io_error_to_string(x_3);
x_5 = l_Lean_Message_getMessageStringEx___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_MessageLog_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
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
static lean_object* _init_l_Lean_MessageLog_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
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
lean_object* l_Lean_MessageLog_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageLog_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageLog_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageLog_HasAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_HasAppend___closed__1;
return x_1;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
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
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(x_2, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(x_1, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentArray_anyMAux___at_Lean_MessageLog_hasErrors___spec__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
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
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
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
x_27 = lean_array_fset(x_8, x_1, x_26);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_27;
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
x_32 = lean_array_fset(x_8, x_1, x_31);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_32;
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
x_35 = lean_array_fset(x_8, x_1, x_34);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_35;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__3(x_5, x_4);
x_7 = x_6;
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = x_8;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__3(x_10, x_9);
x_12 = x_11;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = x_15;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(x_17, x_16);
x_19 = x_18;
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = x_20;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(x_22, x_21);
x_24 = x_23;
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_3);
x_6 = x_4;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(x_7, x_6);
x_9 = x_8;
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_15 = l_Std_PersistentArray_mapMAux___at_Lean_MessageLog_errorsToWarnings___spec__2(x_10);
x_16 = x_11;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at_Lean_MessageLog_errorsToWarnings___spec__4(x_17, x_16);
x_19 = x_18;
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
lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_12 = lean_box(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Std_PersistentArray_push___rarg(x_5, x_8);
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_12 = lean_box(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Std_PersistentArray_push___rarg(x_5, x_8);
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
uint8_t l_Lean_MessageLog_getInfoMessages___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
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
static lean_object* _init_l_Lean_MessageLog_getInfoMessages___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_getInfoMessages___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageLog_getInfoMessages___closed__1;
x_3 = l_Std_PersistentArray_empty___closed__1;
x_4 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_getInfoMessages___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_MessageLog_getInfoMessages___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_getInfoMessages___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MessageLog_getInfoMessages___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_getInfoMessages___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_getInfoMessages___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_getInfoMessages(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2(x_7, x_4);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_foldlMAux___at_Lean_MessageLog_toList___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageLog_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toList(x_1);
lean_dec(x_1);
return x_2;
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
x_2 = l_Lean_MessageData_ofList___closed__3;
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
lean_object* l___private_Lean_Message_1__mkCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_MetavarContext_Inhabited___closed__1;
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
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) unknown constant ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) constant has already been declared ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) declaration type mismatch ");
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
x_1 = lean_mk_string("has type");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("but it is expected to have type");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) declaration type mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) declaration has metavariables ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) declaration has free variables ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) function expected");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) type expected");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__29;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) let-declaration type mismatch ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__32;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) type mismatch at ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__34;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__35;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application type mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__37;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__38;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument has type");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__40;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__41;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("but function has type");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__43;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__44;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) invalid projection");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__46;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__47;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(kernel) ");
return x_1;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__49;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_KernelException_toMessageData___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__50;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_KernelException_toMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_KernelException_toMessageData___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_LocalContext_Inhabited___closed__2;
x_9 = l___private_Lean_Message_1__mkCtx(x_3, x_8, x_2, x_7);
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
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_KernelException_toMessageData___closed__6;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_LocalContext_Inhabited___closed__2;
x_16 = l___private_Lean_Message_1__mkCtx(x_10, x_15, x_2, x_14);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
switch (lean_obj_tag(x_17)) {
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 2);
lean_inc(x_39);
lean_dec(x_37);
x_19 = x_38;
x_20 = x_39;
goto block_35;
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
lean_dec(x_41);
x_19 = x_42;
x_20 = x_43;
goto block_35;
}
default: 
{
lean_object* x_44; 
lean_dec(x_18);
lean_dec(x_17);
x_44 = l_Lean_KernelException_toMessageData___closed__18;
return x_44;
}
}
block_35:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = l_Lean_KernelException_toMessageData___closed__9;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_MessageData_ofList___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_KernelException_toMessageData___closed__12;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_indentExpr(x_18);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_31 = l_Lean_KernelException_toMessageData___closed__15;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_20);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
case 3:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_KernelException_toMessageData___closed__21;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_LocalContext_Inhabited___closed__2;
x_51 = l___private_Lean_Message_1__mkCtx(x_45, x_50, x_2, x_49);
return x_51;
}
case 4:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_KernelException_toMessageData___closed__24;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_LocalContext_Inhabited___closed__2;
x_58 = l___private_Lean_Message_1__mkCtx(x_52, x_57, x_2, x_56);
return x_58;
}
case 5:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 2);
lean_inc(x_61);
lean_dec(x_1);
x_62 = l_Lean_indentExpr(x_61);
x_63 = l_Lean_KernelException_toMessageData___closed__27;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l___private_Lean_Message_1__mkCtx(x_59, x_60, x_2, x_64);
return x_65;
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l_Lean_indentExpr(x_68);
x_70 = l_Lean_KernelException_toMessageData___closed__30;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Message_1__mkCtx(x_66, x_67, x_2, x_71);
return x_72;
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
lean_dec(x_1);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_KernelException_toMessageData___closed__33;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l___private_Lean_Message_1__mkCtx(x_73, x_74, x_2, x_78);
return x_79;
}
case 8:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 2);
lean_inc(x_82);
lean_dec(x_1);
x_83 = l_Lean_indentExpr(x_82);
x_84 = l_Lean_KernelException_toMessageData___closed__36;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l___private_Lean_Message_1__mkCtx(x_80, x_81, x_2, x_85);
return x_86;
}
case 9:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 4);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_indentExpr(x_89);
x_93 = l_Lean_KernelException_toMessageData___closed__39;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_MessageData_ofList___closed__3;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_KernelException_toMessageData___closed__42;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_indentExpr(x_91);
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_95);
x_102 = l_Lean_KernelException_toMessageData___closed__45;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_indentExpr(x_90);
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Lean_Message_1__mkCtx(x_87, x_88, x_2, x_105);
return x_106;
}
case 10:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
lean_dec(x_1);
x_110 = l_Lean_indentExpr(x_109);
x_111 = l_Lean_KernelException_toMessageData___closed__48;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l___private_Lean_Message_1__mkCtx(x_107, x_108, x_2, x_112);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_114 = lean_ctor_get(x_1, 0);
lean_inc(x_114);
lean_dec(x_1);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lean_KernelException_toMessageData___closed__51;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
lean_object* l_Lean_addMessageContextTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_addMessageContextTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_addMessageContextTrans___rarg), 3, 0);
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
x_7 = l_Lean_MetavarContext_Inhabited___closed__1;
x_8 = l_Lean_LocalContext_Inhabited___closed__2;
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
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
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
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_3);
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
lean_object* l_String_splitAux___main___at_Lean_stringToMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint32_t x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_string_utf8_get(x_1, x_3);
x_18 = 10;
x_19 = x_17 == x_18;
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
x_22 = l_List_reverse___rarg(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_3, x_23);
lean_dec(x_3);
x_25 = lean_string_utf8_extract(x_1, x_2, x_24);
lean_dec(x_24);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
x_27 = l_String_splitAux___main___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_List_reverse___rarg(x_28);
return x_29;
}
}
}
}
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___main___at_Lean_stringToMessageData___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_fmt___at_Lean_stringToMessageData___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_stringToMessageData___spec__4(lean_object* x_1) {
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
x_8 = l_List_map___main___at_Lean_stringToMessageData___spec__4(x_5);
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
x_13 = l_List_map___main___at_Lean_stringToMessageData___spec__4(x_10);
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
x_3 = l_List_map___main___at_Lean_stringToMessageData___spec__4(x_2);
x_4 = l_Lean_MessageData_ofList___closed__3;
x_5 = l_Lean_MessageData_joinSep___main(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_String_splitAux___main___at_Lean_stringToMessageData___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___main___at_Lean_stringToMessageData___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* l_Lean_Lean_Message___instance__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_MessageData_coeOfString___closed__1;
x_4 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Lean_Message___instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_stringToMessageData___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lean_Message___instance__5___closed__1;
return x_1;
}
}
lean_object* l_Lean_Lean_Message___instance__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasOfNat___closed__1;
return x_1;
}
}
lean_object* l_Lean_Lean_Message___instance__9___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_map___main___rarg(x_1, x_2);
x_4 = l_Lean_MessageData_ofList(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Lean_Message___instance__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__9___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__10___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l_List_map___main___rarg(x_1, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Lean_Message___instance__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__10___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__10___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lean_Message___instance__10___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__5;
x_2 = l_Lean_mkAppStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Message");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1;
x_2 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3;
x_2 = l_Lean_Name_hasMacroScopes___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4;
x_2 = lean_unsigned_to_nat(125u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("msg!");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__18;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7;
x_2 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Message___hyg_125_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toMessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ToMessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4;
x_7 = l_Lean_addMacroScope(x_5, x_6, x_4);
x_8 = l_Lean_SourceInfo_inhabited___closed__1;
x_9 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3;
x_10 = l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_10);
x_12 = l_Array_empty___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_array_push(x_12, x_1);
x_15 = l_Lean_nullKind___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_push(x_13, x_16);
x_18 = l_Lean_mkAppStx___closed__8;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MessageData");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_158_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5;
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
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__1;
x_18 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = l_Array_iterateMAux___main___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(x_16, x_17, x_18, x_16, x_19, x_20, x_2, x_3);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_23);
x_28 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5;
x_29 = l_Lean_addMacroScope(x_25, x_28, x_24);
x_30 = l_Lean_SourceInfo_inhabited___closed__1;
x_31 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4;
x_32 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_26, x_37);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_27, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_44 = lean_array_push(x_43, x_42);
x_45 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_46 = lean_array_push(x_44, x_45);
x_47 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_21, 0, x_48);
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_53 = l_Array_empty___closed__1;
x_54 = lean_array_push(x_53, x_49);
x_55 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5;
x_56 = l_Lean_addMacroScope(x_52, x_55, x_51);
x_57 = l_Lean_SourceInfo_inhabited___closed__1;
x_58 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4;
x_59 = l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8;
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
x_62 = lean_array_push(x_61, x_60);
x_63 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_53, x_64);
x_66 = l_Lean_nullKind___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_push(x_54, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_71 = lean_array_push(x_70, x_69);
x_72 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_73 = lean_array_push(x_71, x_72);
x_74 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_50);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_21);
if (x_77 == 0)
{
return x_21;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_21, 0);
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_21);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
lean_object* l_Lean_Lean_Message___instance__11_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Lean_Message___instance__11_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__11_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__11___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some ({toMessageData e})");
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__11___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Message___instance__11___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__11___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Message___instance__11___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__11___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_hasCoeOfOptExpr___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Lean_Message___instance__11___rarg___closed__3;
return x_3;
}
}
}
lean_object* l_Lean_Lean_Message___instance__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__11___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Lean_Message___instance__11___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lean_Message___instance__11___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lean_Message___instance__11(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Lean_Message___instance__12_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Lean_Message___instance__12_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Message___instance__12_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<not-available>");
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Message___instance__12___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Message___instance__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Message___instance__12___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Message___instance__12(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Lean_Message___instance__12___closed__3;
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
lean_object* l_Lean_Lean_Message___instance__12___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lean_Message___instance__12(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Position(lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Util_PPExt(lean_object*);
lean_object* initialize_Lean_Util_PPGoal(lean_object*);
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
res = initialize_Lean_Util_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MessageData_nil___closed__1 = _init_l_Lean_MessageData_nil___closed__1();
lean_mark_persistent(l_Lean_MessageData_nil___closed__1);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
l_Lean_MessageData_Inhabited = _init_l_Lean_MessageData_Inhabited();
lean_mark_persistent(l_Lean_MessageData_Inhabited);
l_Lean_MessageData_formatAux___main___closed__1 = _init_l_Lean_MessageData_formatAux___main___closed__1();
lean_mark_persistent(l_Lean_MessageData_formatAux___main___closed__1);
l_Lean_MessageData_formatAux___main___closed__2 = _init_l_Lean_MessageData_formatAux___main___closed__2();
lean_mark_persistent(l_Lean_MessageData_formatAux___main___closed__2);
l_Lean_MessageData_format___closed__1 = _init_l_Lean_MessageData_format___closed__1();
lean_mark_persistent(l_Lean_MessageData_format___closed__1);
l_Lean_MessageData_hasCoeOfOptExpr___closed__1 = _init_l_Lean_MessageData_hasCoeOfOptExpr___closed__1();
lean_mark_persistent(l_Lean_MessageData_hasCoeOfOptExpr___closed__1);
l_Lean_MessageData_coeOfString___closed__1 = _init_l_Lean_MessageData_coeOfString___closed__1();
lean_mark_persistent(l_Lean_MessageData_coeOfString___closed__1);
l_Lean_MessageData_coeOfString___closed__2 = _init_l_Lean_MessageData_coeOfString___closed__2();
lean_mark_persistent(l_Lean_MessageData_coeOfString___closed__2);
l_Lean_MessageData_coeOfString = _init_l_Lean_MessageData_coeOfString();
lean_mark_persistent(l_Lean_MessageData_coeOfString);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2);
l_Lean_MessageData_hasCoeOfArrayExpr___closed__1 = _init_l_Lean_MessageData_hasCoeOfArrayExpr___closed__1();
lean_mark_persistent(l_Lean_MessageData_hasCoeOfArrayExpr___closed__1);
l_Lean_MessageData_hasCoeOfArrayExpr___closed__2 = _init_l_Lean_MessageData_hasCoeOfArrayExpr___closed__2();
lean_mark_persistent(l_Lean_MessageData_hasCoeOfArrayExpr___closed__2);
l_Lean_MessageData_ofList___closed__1 = _init_l_Lean_MessageData_ofList___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__1);
l_Lean_MessageData_ofList___closed__2 = _init_l_Lean_MessageData_ofList___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__2);
l_Lean_MessageData_ofList___closed__3 = _init_l_Lean_MessageData_ofList___closed__3();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__3);
l_Lean_MessageData_ofList___closed__4 = _init_l_Lean_MessageData_ofList___closed__4();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__4);
l_Lean_MessageData_hasCoeOfList___closed__1 = _init_l_Lean_MessageData_hasCoeOfList___closed__1();
lean_mark_persistent(l_Lean_MessageData_hasCoeOfList___closed__1);
l_Lean_MessageData_hasCoeOfList = _init_l_Lean_MessageData_hasCoeOfList();
lean_mark_persistent(l_Lean_MessageData_hasCoeOfList);
l_Lean_MessageData_coeOfList = _init_l_Lean_MessageData_coeOfList();
lean_mark_persistent(l_Lean_MessageData_coeOfList);
l_Lean_Message_toString___closed__1 = _init_l_Lean_Message_toString___closed__1();
lean_mark_persistent(l_Lean_Message_toString___closed__1);
l_Lean_Message_toString___closed__2 = _init_l_Lean_Message_toString___closed__2();
lean_mark_persistent(l_Lean_Message_toString___closed__2);
l_Lean_Message_toString___closed__3 = _init_l_Lean_Message_toString___closed__3();
lean_mark_persistent(l_Lean_Message_toString___closed__3);
l_Lean_Message_toString___closed__4 = _init_l_Lean_Message_toString___closed__4();
lean_mark_persistent(l_Lean_Message_toString___closed__4);
l_Lean_Message_toString___closed__5 = _init_l_Lean_Message_toString___closed__5();
lean_mark_persistent(l_Lean_Message_toString___closed__5);
l_Lean_Message_Inhabited___closed__1 = _init_l_Lean_Message_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Message_Inhabited___closed__1);
l_Lean_Message_Inhabited___closed__2 = _init_l_Lean_Message_Inhabited___closed__2();
lean_mark_persistent(l_Lean_Message_Inhabited___closed__2);
l_Lean_Message_Inhabited = _init_l_Lean_Message_Inhabited();
lean_mark_persistent(l_Lean_Message_Inhabited);
l_Lean_Message_getMessageStringEx___closed__1 = _init_l_Lean_Message_getMessageStringEx___closed__1();
lean_mark_persistent(l_Lean_Message_getMessageStringEx___closed__1);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
l_Lean_MessageLog_Inhabited = _init_l_Lean_MessageLog_Inhabited();
lean_mark_persistent(l_Lean_MessageLog_Inhabited);
l_Lean_MessageLog_HasAppend___closed__1 = _init_l_Lean_MessageLog_HasAppend___closed__1();
lean_mark_persistent(l_Lean_MessageLog_HasAppend___closed__1);
l_Lean_MessageLog_HasAppend = _init_l_Lean_MessageLog_HasAppend();
lean_mark_persistent(l_Lean_MessageLog_HasAppend);
l_Lean_MessageLog_getInfoMessages___closed__1 = _init_l_Lean_MessageLog_getInfoMessages___closed__1();
lean_mark_persistent(l_Lean_MessageLog_getInfoMessages___closed__1);
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
l_Lean_KernelException_toMessageData___closed__51 = _init_l_Lean_KernelException_toMessageData___closed__51();
lean_mark_persistent(l_Lean_KernelException_toMessageData___closed__51);
l_Lean_Lean_Message___instance__5___closed__1 = _init_l_Lean_Lean_Message___instance__5___closed__1();
lean_mark_persistent(l_Lean_Lean_Message___instance__5___closed__1);
l_Lean_Lean_Message___instance__5 = _init_l_Lean_Lean_Message___instance__5();
lean_mark_persistent(l_Lean_Lean_Message___instance__5);
l_Lean_Lean_Message___instance__8 = _init_l_Lean_Lean_Message___instance__8();
lean_mark_persistent(l_Lean_Lean_Message___instance__8);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__1);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__2);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__3);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__4);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__5);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__6);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__7);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__8);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__9);
l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10 = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125____closed__10);
l_Lean___kind_term____x40_Lean_Message___hyg_125_ = _init_l_Lean___kind_term____x40_Lean_Message___hyg_125_();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Message___hyg_125_);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__1);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__2);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__3);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__4);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__5);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__6);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__7);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__8);
l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____lambda__1___closed__9);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__1);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__2);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__3);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__4);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__5);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__6);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__7);
l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8 = _init_l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Message___hyg_158____closed__8);
l_Lean_Lean_Message___instance__11___rarg___closed__1 = _init_l_Lean_Lean_Message___instance__11___rarg___closed__1();
lean_mark_persistent(l_Lean_Lean_Message___instance__11___rarg___closed__1);
l_Lean_Lean_Message___instance__11___rarg___closed__2 = _init_l_Lean_Lean_Message___instance__11___rarg___closed__2();
lean_mark_persistent(l_Lean_Lean_Message___instance__11___rarg___closed__2);
l_Lean_Lean_Message___instance__11___rarg___closed__3 = _init_l_Lean_Lean_Message___instance__11___rarg___closed__3();
lean_mark_persistent(l_Lean_Lean_Message___instance__11___rarg___closed__3);
l_Lean_Lean_Message___instance__12___closed__1 = _init_l_Lean_Lean_Message___instance__12___closed__1();
lean_mark_persistent(l_Lean_Lean_Message___instance__12___closed__1);
l_Lean_Lean_Message___instance__12___closed__2 = _init_l_Lean_Lean_Message___instance__12___closed__2();
lean_mark_persistent(l_Lean_Lean_Message___instance__12___closed__2);
l_Lean_Lean_Message___instance__12___closed__3 = _init_l_Lean_Lean_Message___instance__12___closed__3();
lean_mark_persistent(l_Lean_Lean_Message___instance__12___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
