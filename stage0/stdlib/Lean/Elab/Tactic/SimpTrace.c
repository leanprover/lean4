// Lean compiler output
// Module: Lean.Elab.Tactic.SimpTrace
// Imports: public import Lean.Elab.ElabRules public import Lean.Elab.Tactic.Simp public import Lean.Meta.Tactic.TryThis public import Lean.LibrarySuggestions.Basic
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 179, 144, 54, 113, 159, 205, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(87, 30, 159, 74, 102, 214, 91, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object*, lean_object*);
static const lean_array_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected identifier"};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value)}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0 = (const lean_object*)&l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value;
static const lean_array_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 96, 113, 105, 41, 106, 130, 154)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 84, 117, 30, 74, 67, 74, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp_all!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpAllTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 138, 193, 72, 181, 178, 244, 77)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSimpAllTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 119, 44, 227, 45, 220, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dsimpAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dsimp!"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dsimpTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 29, 147, 115, 237, 79, 62, 93)}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalDSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 218, 74, 127, 38, 51, 185, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(lean_object* v_as_12_, size_t v_i_13_, size_t v_stop_14_, lean_object* v_b_15_){
_start:
{
lean_object* v___y_17_; uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_eq(v_i_13_, v_stop_14_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_uget_borrowed(v_as_12_, v_i_13_);
v___x_24_ = l_Lean_Syntax_getArg(v___x_23_, v___x_22_);
lean_inc(v___x_23_);
v___x_25_ = l_Lean_Syntax_getKind(v___x_23_);
if (lean_obj_tag(v___x_25_) == 1)
{
lean_object* v_pre_26_; 
v_pre_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_pre_26_);
if (lean_obj_tag(v_pre_26_) == 1)
{
lean_object* v_pre_27_; 
v_pre_27_ = lean_ctor_get(v_pre_26_, 0);
lean_inc(v_pre_27_);
if (lean_obj_tag(v_pre_27_) == 1)
{
lean_object* v_pre_28_; 
v_pre_28_ = lean_ctor_get(v_pre_27_, 0);
lean_inc(v_pre_28_);
if (lean_obj_tag(v_pre_28_) == 1)
{
lean_object* v_pre_29_; 
v_pre_29_ = lean_ctor_get(v_pre_28_, 0);
if (lean_obj_tag(v_pre_29_) == 0)
{
lean_object* v_str_30_; lean_object* v_str_31_; lean_object* v_str_32_; lean_object* v_str_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_str_30_ = lean_ctor_get(v___x_25_, 1);
lean_inc_ref(v_str_30_);
lean_dec_ref_known(v___x_25_, 2);
v_str_31_ = lean_ctor_get(v_pre_26_, 1);
lean_inc_ref(v_str_31_);
lean_dec_ref_known(v_pre_26_, 2);
v_str_32_ = lean_ctor_get(v_pre_27_, 1);
lean_inc_ref(v_str_32_);
lean_dec_ref_known(v_pre_27_, 2);
v_str_33_ = lean_ctor_get(v_pre_28_, 1);
lean_inc_ref(v_str_33_);
lean_dec_ref_known(v_pre_28_, 2);
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_35_ = lean_string_dec_eq(v_str_33_, v___x_34_);
lean_dec_ref(v_str_33_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec_ref(v_str_32_);
lean_dec_ref(v_str_31_);
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_36_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_36_;
goto v___jp_16_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_38_ = lean_string_dec_eq(v_str_32_, v___x_37_);
lean_dec_ref(v_str_32_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_str_31_);
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_39_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_39_;
goto v___jp_16_;
}
else
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_41_ = lean_string_dec_eq(v_str_31_, v___x_40_);
lean_dec_ref(v_str_31_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_42_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_42_;
goto v___jp_16_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3));
v___x_44_ = lean_string_dec_eq(v_str_30_, v___x_43_);
lean_dec_ref(v_str_30_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_45_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_45_;
goto v___jp_16_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = l_Lean_Syntax_getArg(v___x_24_, v___x_46_);
v___x_48_ = l_Lean_Syntax_getKind(v___x_24_);
if (lean_obj_tag(v___x_48_) == 1)
{
lean_object* v_pre_49_; 
v_pre_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_pre_49_);
if (lean_obj_tag(v_pre_49_) == 1)
{
lean_object* v_pre_50_; 
v_pre_50_ = lean_ctor_get(v_pre_49_, 0);
lean_inc(v_pre_50_);
if (lean_obj_tag(v_pre_50_) == 1)
{
lean_object* v_pre_51_; 
v_pre_51_ = lean_ctor_get(v_pre_50_, 0);
lean_inc(v_pre_51_);
if (lean_obj_tag(v_pre_51_) == 1)
{
lean_object* v_pre_52_; 
v_pre_52_ = lean_ctor_get(v_pre_51_, 0);
if (lean_obj_tag(v_pre_52_) == 0)
{
lean_object* v_str_53_; lean_object* v_str_54_; lean_object* v_str_55_; lean_object* v_str_56_; uint8_t v___x_57_; 
v_str_53_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_str_53_);
lean_dec_ref_known(v___x_48_, 2);
v_str_54_ = lean_ctor_get(v_pre_49_, 1);
lean_inc_ref(v_str_54_);
lean_dec_ref_known(v_pre_49_, 2);
v_str_55_ = lean_ctor_get(v_pre_50_, 1);
lean_inc_ref(v_str_55_);
lean_dec_ref_known(v_pre_50_, 2);
v_str_56_ = lean_ctor_get(v_pre_51_, 1);
lean_inc_ref(v_str_56_);
lean_dec_ref_known(v_pre_51_, 2);
v___x_57_ = lean_string_dec_eq(v_str_56_, v___x_34_);
lean_dec_ref(v_str_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v_str_55_);
lean_dec_ref(v_str_54_);
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_58_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_58_;
goto v___jp_16_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = lean_string_dec_eq(v_str_55_, v___x_37_);
lean_dec_ref(v_str_55_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v_str_54_);
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_60_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_60_;
goto v___jp_16_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = lean_string_dec_eq(v_str_54_, v___x_40_);
lean_dec_ref(v_str_54_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_62_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_62_;
goto v___jp_16_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4));
v___x_64_ = lean_string_dec_eq(v_str_53_, v___x_63_);
lean_dec_ref(v_str_53_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_65_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_65_;
goto v___jp_16_;
}
else
{
lean_object* v___x_66_; lean_object* v_id_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_66_ = l_Lean_Syntax_getId(v___x_47_);
lean_dec(v___x_47_);
v_id_67_ = l_Lean_Name_eraseMacroScopes(v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6));
v___x_69_ = lean_name_eq(v_id_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8));
v___x_71_ = lean_name_eq(v_id_67_, v___x_70_);
lean_dec(v_id_67_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_inc(v___x_23_);
v___x_72_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_72_;
goto v___jp_16_;
}
else
{
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
}
else
{
lean_dec(v_id_67_);
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
}
}
}
}
}
else
{
lean_object* v___x_73_; 
lean_dec_ref_known(v_pre_51_, 2);
lean_dec_ref_known(v_pre_50_, 2);
lean_dec_ref_known(v_pre_49_, 2);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_73_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_73_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_74_; 
lean_dec_ref_known(v_pre_50_, 2);
lean_dec(v_pre_51_);
lean_dec_ref_known(v_pre_49_, 2);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_74_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_74_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec_ref_known(v_pre_49_, 2);
lean_dec(v_pre_50_);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_75_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_75_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_76_; 
lean_dec(v_pre_49_);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_76_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_76_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v___x_48_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_77_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_77_;
goto v___jp_16_;
}
}
}
}
}
}
else
{
lean_object* v___x_78_; 
lean_dec_ref_known(v_pre_28_, 2);
lean_dec_ref_known(v_pre_27_, 2);
lean_dec_ref_known(v_pre_26_, 2);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_78_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_78_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec_ref_known(v_pre_27_, 2);
lean_dec(v_pre_28_);
lean_dec_ref_known(v_pre_26_, 2);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_79_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_79_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec_ref_known(v_pre_26_, 2);
lean_dec(v_pre_27_);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_80_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_80_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v_pre_26_);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_81_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_81_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_82_; 
lean_dec(v___x_25_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_82_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_82_;
goto v___jp_16_;
}
}
else
{
return v_b_15_;
}
v___jp_16_:
{
size_t v___x_18_; size_t v___x_19_; 
v___x_18_ = ((size_t)1ULL);
v___x_19_ = lean_usize_add(v_i_13_, v___x_18_);
v_i_13_ = v___x_19_;
v_b_15_ = v___y_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object* v_cfg_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_nullNode_95_; lean_object* v___y_97_; lean_object* v_configItems_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v_nullNode_95_ = l_Lean_Syntax_getArg(v_cfg_92_, v___x_94_);
v_configItems_101_ = l_Lean_Syntax_getArgs(v_nullNode_95_);
v___x_102_ = lean_array_get_size(v_configItems_101_);
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_104_ = lean_nat_dec_lt(v___x_94_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_103_;
goto v___jp_96_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_105_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_103_;
goto v___jp_96_;
}
else
{
size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_102_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_106_, v___x_107_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_108_;
goto v___jp_96_;
}
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_102_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_109_, v___x_110_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_111_;
goto v___jp_96_;
}
}
v___jp_96_:
{
lean_object* v_newNullNode_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_newNullNode_98_ = l_Lean_Syntax_setArgs(v_nullNode_95_, v___y_97_);
v___x_99_ = l_Lean_Syntax_setArg(v_cfg_92_, v___x_94_, v_newNullNode_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_115_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_129_, lean_object* v_usedSimps_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_stx_136_; lean_object* v___x_137_; 
v_stx_136_ = l_Lean_Syntax_unsetTrailing(v_stx_129_);
v___x_137_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_136_, v_usedSimps_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_137_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_154_, lean_object* v_usedSimps_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_154_, v_usedSimps_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec_ref(v_usedSimps_155_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_192_, lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(v___x_192_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_201_, lean_object* v_x_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_33587__boxed_208_; lean_object* v_res_209_; 
v___x_33587__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33587__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v_x_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_210_, lean_object* v___x_211_, uint8_t v___x_212_, lean_object* v___y_213_, lean_object* v_simprocs_214_, lean_object* v_discharge_x3f_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
if (lean_obj_tag(v___y_210_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_211_);
v___x_226_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_212_);
v___x_227_ = l_Lean_Elab_Tactic_simpLocation(v___y_213_, v_simprocs_214_, v_discharge_x3f_215_, v___x_226_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_val_228_ = lean_ctor_get(v___y_210_, 0);
v___x_229_ = l_Lean_Elab_Tactic_expandLocation(v_val_228_);
v___x_230_ = l_Lean_Elab_Tactic_simpLocation(v___y_213_, v_simprocs_214_, v_discharge_x3f_215_, v___x_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___y_234_, lean_object* v_simprocs_235_, lean_object* v_discharge_x3f_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___x_33614__boxed_246_; lean_object* v_res_247_; 
v___x_33614__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33614__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___x_232_);
lean_dec(v___y_231_);
return v_res_247_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_mkArray0___redArg();
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_258_, lean_object* v_as_x27_259_, lean_object* v_b_260_, lean_object* v___y_261_){
_start:
{
if (lean_obj_tag(v_as_x27_259_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_b_260_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v_ref_266_; uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_head_264_ = lean_ctor_get(v_as_x27_259_, 0);
v_tail_265_ = lean_ctor_get(v_as_x27_259_, 1);
v_ref_266_ = lean_ctor_get(v___y_261_, 2);
v___x_267_ = 1;
v___x_268_ = 0;
v___x_269_ = l_Lean_SourceInfo_fromRef(v_ref_266_, v___x_268_);
v___x_270_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_271_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_272_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_269_);
v___x_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_273_, 0, v___x_269_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_272_);
lean_inc(v_head_264_);
v___x_274_ = l_Lean_mkCIdentFrom(v___x_258_, v_head_264_, v___x_267_);
lean_inc_ref(v___x_273_);
v___x_275_ = l_Lean_Syntax_node3(v___x_269_, v___x_270_, v___x_273_, v___x_273_, v___x_274_);
v___x_276_ = lean_array_push(v_b_260_, v___x_275_);
v_as_x27_259_ = v_tail_265_;
v_b_260_ = v___x_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_278_, lean_object* v_as_x27_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_278_, v_as_x27_279_, v_b_280_, v___y_281_);
lean_dec_ref(v___y_281_);
lean_dec(v_as_x27_279_);
lean_dec(v___x_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v_fst_288_; uint8_t v___x_289_; 
v_head_286_ = lean_ctor_get(v_x_284_, 0);
v_tail_287_ = lean_ctor_get(v_x_284_, 1);
v_fst_288_ = lean_ctor_get(v_head_286_, 0);
v___x_289_ = l_Lean_isPrivateName(v_fst_288_);
if (v___x_289_ == 0)
{
v_x_284_ = v_tail_287_;
goto _start;
}
else
{
lean_object* v___x_291_; 
lean_inc(v_head_286_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v_head_286_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_292_);
lean_dec(v_x_292_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_294_, lean_object* v_opt_295_){
_start:
{
lean_object* v_name_296_; lean_object* v_defValue_297_; lean_object* v_map_298_; lean_object* v___x_299_; 
v_name_296_ = lean_ctor_get(v_opt_295_, 0);
v_defValue_297_ = lean_ctor_get(v_opt_295_, 1);
v_map_298_ = lean_ctor_get(v_opts_294_, 0);
v___x_299_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_298_, v_name_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = lean_unbox(v_defValue_297_);
return v___x_300_;
}
else
{
lean_object* v_val_301_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_299_, 1);
if (lean_obj_tag(v_val_301_) == 1)
{
uint8_t v_v_302_; 
v_v_302_ = lean_ctor_get_uint8(v_val_301_, 0);
lean_dec_ref_known(v_val_301_, 0);
return v_v_302_;
}
else
{
uint8_t v___x_303_; 
lean_dec(v_val_301_);
v___x_303_ = lean_unbox(v_defValue_297_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_304_, lean_object* v_opt_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_304_, v_opt_305_);
lean_dec_ref(v_opt_305_);
lean_dec_ref(v_opts_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_309_);
v___x_312_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_311_, v_opt_308_);
lean_dec_ref(v___x_311_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_315_, v___y_316_);
lean_dec_ref(v___y_316_);
lean_dec_ref(v_opt_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; uint8_t v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_toCold_330_; lean_object* v_mctx_331_; lean_object* v_lctx_332_; lean_object* v_options_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = 0;
v_env_328_ = l_Lean_Environment_setRecordingDeps(v_env_326_, v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_321_);
v_toCold_330_ = lean_ctor_get(v___y_322_, 0);
v_mctx_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_331_);
lean_dec(v___x_329_);
v_lctx_332_ = lean_ctor_get(v___y_320_, 2);
v_options_333_ = lean_ctor_get(v_toCold_330_, 2);
lean_inc_ref(v_options_333_);
lean_inc_ref(v_lctx_332_);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v_env_328_);
lean_ctor_set(v___x_334_, 1, v_mctx_331_);
lean_ctor_set(v___x_334_, 2, v_lctx_332_);
lean_ctor_set(v___x_334_, 3, v_options_333_);
v___x_335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_msgData_319_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_351_, uint8_t v___y_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 1)
{
lean_object* v_pre_354_; 
v_pre_354_ = lean_ctor_get(v_x_353_, 0);
switch(lean_obj_tag(v_pre_354_))
{
case 1:
{
lean_object* v_pre_355_; 
v_pre_355_ = lean_ctor_get(v_pre_354_, 0);
switch(lean_obj_tag(v_pre_355_))
{
case 0:
{
lean_object* v_str_356_; lean_object* v_str_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_str_356_ = lean_ctor_get(v_x_353_, 1);
v_str_357_ = lean_ctor_get(v_pre_354_, 1);
v___x_358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_359_ = lean_string_dec_eq(v_str_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_361_ = lean_string_dec_eq(v_str_357_, v___x_360_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_363_ = lean_string_dec_eq(v_str_356_, v___x_362_);
if (v___x_363_ == 0)
{
return v___x_363_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
else
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_365_ = lean_string_dec_eq(v_str_356_, v___x_364_);
if (v___x_365_ == 0)
{
return v___x_365_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
case 1:
{
lean_object* v_pre_366_; 
v_pre_366_ = lean_ctor_get(v_pre_355_, 0);
if (lean_obj_tag(v_pre_366_) == 0)
{
lean_object* v_str_367_; lean_object* v_str_368_; lean_object* v_str_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_str_367_ = lean_ctor_get(v_x_353_, 1);
v_str_368_ = lean_ctor_get(v_pre_354_, 1);
v_str_369_ = lean_ctor_get(v_pre_355_, 1);
v___x_370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_371_ = lean_string_dec_eq(v_str_369_, v___x_370_);
if (v___x_371_ == 0)
{
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_373_ = lean_string_dec_eq(v_str_368_, v___x_372_);
if (v___x_373_ == 0)
{
return v___x_373_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_375_ = lean_string_dec_eq(v_str_367_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
}
else
{
return v___y_352_;
}
}
default: 
{
return v___y_352_;
}
}
}
case 0:
{
lean_object* v_str_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_str_376_ = lean_ctor_get(v_x_353_, 1);
v___x_377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_378_ = lean_string_dec_eq(v_str_376_, v___x_377_);
if (v___x_378_ == 0)
{
return v___x_378_;
}
else
{
return v_suppressElabErrors_351_;
}
}
default: 
{
return v___y_352_;
}
}
}
else
{
return v___y_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_379_, lean_object* v___y_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_suppressElabErrors_boxed_382_; uint8_t v___y_33817__boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v_suppressElabErrors_boxed_382_ = lean_unbox(v_suppressElabErrors_379_);
v___y_33817__boxed_383_ = lean_unbox(v___y_380_);
v_res_384_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_382_, v___y_33817__boxed_383_, v_x_381_);
lean_dec(v_x_381_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_387_, lean_object* v_msgData_388_, uint8_t v_severity_389_, uint8_t v_isSilent_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; uint8_t v___y_403_; lean_object* v_toCold_404_; lean_object* v___y_405_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___y_439_; uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; uint8_t v___y_471_; uint8_t v___y_472_; uint8_t v___y_473_; uint8_t v___x_484_; uint8_t v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; uint8_t v___y_490_; uint8_t v___x_498_; 
v___x_484_ = 2;
v___x_498_ = l_Lean_instBEqMessageSeverity_beq(v_severity_389_, v___x_484_);
if (v___x_498_ == 0)
{
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
else
{
uint8_t v___x_499_; 
lean_inc_ref(v_msgData_388_);
v___x_499_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_388_);
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
v___jp_396_:
{
lean_object* v_currNamespace_406_; lean_object* v_openDecls_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_env_412_; lean_object* v_nextMacroScope_413_; lean_object* v_ngen_414_; lean_object* v_auxDeclNGen_415_; lean_object* v_traceState_416_; lean_object* v_cache_417_; lean_object* v_recordedDeps_418_; lean_object* v_messages_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
v_currNamespace_406_ = lean_ctor_get(v_toCold_404_, 4);
v_openDecls_407_ = lean_ctor_get(v_toCold_404_, 5);
lean_inc(v_openDecls_407_);
lean_inc(v_currNamespace_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_currNamespace_406_);
lean_ctor_set(v___x_408_, 1, v_openDecls_407_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___y_402_);
lean_inc_ref(v___y_397_);
lean_inc_ref(v___y_400_);
v___x_410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_410_, 0, v___y_400_);
lean_ctor_set(v___x_410_, 1, v___y_401_);
lean_ctor_set(v___x_410_, 2, v___y_399_);
lean_ctor_set(v___x_410_, 3, v___y_397_);
lean_ctor_set(v___x_410_, 4, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5, v___y_403_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 1, v___y_398_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 2, v_isSilent_390_);
v___x_411_ = lean_st_ref_take(v___y_405_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
v_nextMacroScope_413_ = lean_ctor_get(v___x_411_, 1);
v_ngen_414_ = lean_ctor_get(v___x_411_, 2);
v_auxDeclNGen_415_ = lean_ctor_get(v___x_411_, 3);
v_traceState_416_ = lean_ctor_get(v___x_411_, 4);
v_cache_417_ = lean_ctor_get(v___x_411_, 5);
v_recordedDeps_418_ = lean_ctor_get(v___x_411_, 6);
v_messages_419_ = lean_ctor_get(v___x_411_, 7);
v_infoState_420_ = lean_ctor_get(v___x_411_, 8);
v_snapshotTasks_421_ = lean_ctor_get(v___x_411_, 9);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_432_ == 0)
{
v___x_423_ = v___x_411_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_messages_419_);
lean_inc(v_recordedDeps_418_);
lean_inc(v_cache_417_);
lean_inc(v_traceState_416_);
lean_inc(v_auxDeclNGen_415_);
lean_inc(v_ngen_414_);
lean_inc(v_nextMacroScope_413_);
lean_inc(v_env_412_);
lean_dec(v___x_411_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = lean_box(0);
v___x_426_ = l_Lean_MessageLog_add(v___x_410_, v_messages_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 7, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_recordedDeps_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_snapshotTasks_421_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_st_ref_put(v___y_405_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_425_);
return v___x_430_;
}
}
}
v___jp_433_:
{
lean_object* v_fileName_442_; lean_object* v_fileMap_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_459_; 
v_fileName_442_ = lean_ctor_get(v___y_439_, 0);
v_fileMap_443_ = lean_ctor_get(v___y_439_, 1);
v___x_444_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_388_);
v___x_445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_444_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_459_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_459_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc_ref_n(v_fileMap_443_, 2);
v___x_450_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_437_);
lean_dec(v___y_437_);
v___x_451_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_441_);
lean_dec(v___y_441_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_448_);
lean_dec_ref(v___y_434_);
v___y_397_ = v___x_453_;
v___y_398_ = v___y_438_;
v___y_399_ = v___x_452_;
v___y_400_ = v_fileName_442_;
v___y_401_ = v___x_450_;
v___y_402_ = v_a_446_;
v___y_403_ = v___y_440_;
v_toCold_404_ = v___y_435_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
else
{
uint8_t v___x_454_; 
lean_inc(v_a_446_);
v___x_454_ = l_Lean_MessageData_hasTag(v___y_434_, v_a_446_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref_known(v___x_452_, 1);
lean_dec_ref(v___x_450_);
lean_dec(v_a_446_);
v___x_455_ = lean_box(0);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_455_);
v___x_457_ = v___x_448_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_del_object(v___x_448_);
v___y_397_ = v___x_453_;
v___y_398_ = v___y_438_;
v___y_399_ = v___x_452_;
v___y_400_ = v_fileName_442_;
v___y_401_ = v___x_450_;
v___y_402_ = v_a_446_;
v___y_403_ = v___y_440_;
v_toCold_404_ = v___y_435_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Syntax_getTailPos_x3f(v___y_465_, v___y_466_);
lean_dec(v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_inc(v___y_467_);
v___y_434_ = v___y_461_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_467_;
v___y_438_ = v___y_464_;
v___y_439_ = v___y_463_;
v___y_440_ = v___y_466_;
v___y_441_ = v___y_467_;
goto v___jp_433_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___y_434_ = v___y_461_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_467_;
v___y_438_ = v___y_464_;
v___y_439_ = v___y_463_;
v___y_440_ = v___y_466_;
v___y_441_ = v_val_469_;
goto v___jp_433_;
}
}
v___jp_470_:
{
lean_object* v_toCold_474_; lean_object* v_ref_475_; uint8_t v_suppressElabErrors_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v_ref_480_; lean_object* v___x_481_; 
v_toCold_474_ = lean_ctor_get(v___y_393_, 0);
v_ref_475_ = lean_ctor_get(v___y_393_, 2);
v_suppressElabErrors_476_ = lean_ctor_get_uint8(v___y_393_, sizeof(void*)*3 + 2);
v___x_477_ = lean_box(v_suppressElabErrors_476_);
v___x_478_ = lean_box(v___y_471_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_479_, 0, v___x_477_);
lean_closure_set(v___f_479_, 1, v___x_478_);
v_ref_480_ = l_Lean_replaceRef(v_ref_387_, v_ref_475_);
v___x_481_ = l_Lean_Syntax_getPos_x3f(v_ref_480_, v___y_472_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___y_461_ = v___f_479_;
v___y_462_ = v_suppressElabErrors_476_;
v___y_463_ = v_toCold_474_;
v___y_464_ = v___y_473_;
v___y_465_ = v_ref_480_;
v___y_466_ = v___y_472_;
v___y_467_ = v___x_482_;
goto v___jp_460_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_481_, 1);
v___y_461_ = v___f_479_;
v___y_462_ = v_suppressElabErrors_476_;
v___y_463_ = v_toCold_474_;
v___y_464_ = v___y_473_;
v___y_465_ = v_ref_480_;
v___y_466_ = v___y_472_;
v___y_467_ = v_val_483_;
goto v___jp_460_;
}
}
v___jp_485_:
{
if (v___y_488_ == 0)
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_487_;
v___y_473_ = v_severity_389_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_487_;
v___y_473_ = v___x_484_;
goto v___jp_470_;
}
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
uint8_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 1;
v___x_492_ = l_Lean_instBEqMessageSeverity_beq(v_severity_389_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_486_ = v___y_490_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_492_;
goto v___jp_485_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_393_);
v___x_494_ = l_Lean_warningAsError;
v___x_495_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_493_, v___x_494_);
lean_dec_ref(v___x_493_);
v___y_486_ = v___y_490_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_495_;
goto v___jp_485_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v_msgData_388_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_500_, lean_object* v_msgData_501_, lean_object* v_severity_502_, lean_object* v_isSilent_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_severity_boxed_509_; uint8_t v_isSilent_boxed_510_; lean_object* v_res_511_; 
v_severity_boxed_509_ = lean_unbox(v_severity_502_);
v_isSilent_boxed_510_ = lean_unbox(v_isSilent_503_);
v_res_511_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_500_, v_msgData_501_, v_severity_boxed_509_, v_isSilent_boxed_510_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v_ref_500_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_512_, uint8_t v_severity_513_, uint8_t v_isSilent_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_ref_524_; lean_object* v___x_525_; 
v_ref_524_ = lean_ctor_get(v___y_521_, 2);
v___x_525_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_524_, v_msgData_512_, v_severity_513_, v_isSilent_514_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_526_, lean_object* v_severity_527_, lean_object* v_isSilent_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_severity_boxed_538_; uint8_t v_isSilent_boxed_539_; lean_object* v_res_540_; 
v_severity_boxed_538_ = lean_unbox(v_severity_527_);
v_isSilent_boxed_539_ = lean_unbox(v_isSilent_528_);
v_res_540_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_526_, v_severity_boxed_538_, v_isSilent_boxed_539_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = 1;
v___x_552_ = 0;
v___x_553_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_541_, v___x_551_, v___x_552_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_604_; 
v___x_581_ = lean_st_ref_get(v___y_579_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_581_);
v___x_583_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_584_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_583_, v___y_578_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_604_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_604_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v_isExporting_594_; 
v_isExporting_594_ = lean_ctor_get_uint8(v_env_582_, sizeof(void*)*13);
lean_dec_ref(v_env_582_);
if (v_isExporting_594_ == 0)
{
lean_dec(v_a_585_);
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_isPrivateName(v_id_571_);
if (v___x_595_ == 0)
{
lean_dec(v_a_585_);
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_596_ == 0)
{
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_587_);
v___x_597_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_598_ = 0;
v___x_599_ = l_Lean_MessageData_ofConstName(v_id_571_, v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_602_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_603_;
}
}
}
v___jp_589_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_box(0);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_616_, uint8_t v_enableLog_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_toCold_628_; lean_object* v_env_629_; lean_object* v_currNamespace_630_; lean_object* v_openDecls_631_; lean_object* v___x_632_; lean_object* v_res_633_; lean_object* v___x_634_; 
v___x_627_ = lean_st_ref_get(v___y_625_);
v_toCold_628_ = lean_ctor_get(v___y_624_, 0);
v_env_629_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_627_);
v_currNamespace_630_ = lean_ctor_get(v_toCold_628_, 4);
v_openDecls_631_ = lean_ctor_get(v_toCold_628_, 5);
v___x_632_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_624_);
lean_inc(v_openDecls_631_);
lean_inc(v_currNamespace_630_);
v_res_633_ = l_Lean_ResolveName_resolveGlobalName(v_env_629_, v___x_632_, v_currNamespace_630_, v_openDecls_631_, v_id_616_);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_st_ref_get(v___y_625_);
if (v_enableLog_617_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v___x_634_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_res_633_);
return v___x_635_;
}
else
{
lean_object* v_env_636_; uint8_t v_isExporting_637_; 
v_env_636_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_634_);
v_isExporting_637_ = lean_ctor_get_uint8(v_env_636_, sizeof(void*)*13);
lean_dec_ref(v_env_636_);
if (v_isExporting_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_res_633_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_633_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v_fst_641_; lean_object* v___x_642_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v_fst_641_ = lean_ctor_get(v_val_640_, 0);
lean_inc(v_fst_641_);
lean_dec(v_val_640_);
v___x_642_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_641_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___x_642_, 0);
lean_dec(v_unused_650_);
v___x_644_ = v___x_642_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___x_642_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_res_633_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_res_633_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_res_633_);
v_a_651_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_642_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_642_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v___x_639_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_res_633_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_660_, lean_object* v_enableLog_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_enableLog_boxed_671_; lean_object* v_res_672_; 
v_enableLog_boxed_671_ = lean_unbox(v_enableLog_661_);
v_res_672_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_660_, v_enableLog_boxed_671_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
if (lean_obj_tag(v_a_673_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_List_reverse___redArg(v_a_674_);
return v___x_675_;
}
else
{
lean_object* v_head_676_; lean_object* v_tail_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_688_; 
v_head_676_ = lean_ctor_get(v_a_673_, 0);
v_tail_677_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_688_ == 0)
{
v___x_679_ = v_a_673_;
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_tail_677_);
lean_inc(v_head_676_);
lean_dec(v_a_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_snd_681_; uint8_t v___x_682_; 
v_snd_681_ = lean_ctor_get(v_head_676_, 1);
v___x_682_ = l_List_isEmpty___redArg(v_snd_681_);
if (v___x_682_ == 0)
{
lean_del_object(v___x_679_);
lean_dec(v_head_676_);
v_a_673_ = v_tail_677_;
goto _start;
}
else
{
lean_object* v___x_685_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v_a_674_);
v___x_685_ = v___x_679_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_head_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_674_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v_a_673_ = v_tail_677_;
v_a_674_ = v___x_685_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
if (lean_obj_tag(v_a_689_) == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_List_reverse___redArg(v_a_690_);
return v___x_691_;
}
else
{
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_head_692_ = lean_ctor_get(v_a_689_, 0);
v_tail_693_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v_a_689_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_tail_693_);
lean_inc(v_head_692_);
lean_dec(v_a_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; lean_object* v___x_699_; 
v_fst_697_ = lean_ctor_get(v_head_692_, 0);
lean_inc(v_fst_697_);
lean_dec(v_head_692_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_690_);
lean_ctor_set(v___x_695_, 0, v_fst_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_690_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_689_ = v_tail_693_;
v_a_690_ = v___x_699_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_ref_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_ref_709_ = lean_ctor_get(v___y_706_, 2);
v___x_710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_719_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_ref_709_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_ref_709_);
lean_ctor_set(v___x_715_, 1, v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 1);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_toCold_738_; lean_object* v_currRecDepth_739_; lean_object* v_ref_740_; uint16_t v_optionFlags_741_; uint8_t v_suppressElabErrors_742_; uint8_t v_isRecordingDeps_743_; lean_object* v_ref_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_toCold_738_ = lean_ctor_get(v___y_735_, 0);
v_currRecDepth_739_ = lean_ctor_get(v___y_735_, 1);
v_ref_740_ = lean_ctor_get(v___y_735_, 2);
v_optionFlags_741_ = lean_ctor_get_uint16(v___y_735_, sizeof(void*)*3);
v_suppressElabErrors_742_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*3 + 2);
v_isRecordingDeps_743_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*3 + 3);
v_ref_744_ = l_Lean_replaceRef(v_ref_727_, v_ref_740_);
lean_inc(v_currRecDepth_739_);
lean_inc_ref(v_toCold_738_);
v___x_745_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_745_, 0, v_toCold_738_);
lean_ctor_set(v___x_745_, 1, v_currRecDepth_739_);
lean_ctor_set(v___x_745_, 2, v_ref_744_);
lean_ctor_set_uint16(v___x_745_, sizeof(void*)*3, v_optionFlags_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 2, v_suppressElabErrors_742_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 3, v_isRecordingDeps_743_);
v___x_746_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_728_, v___y_733_, v___y_734_, v___x_745_, v___y_736_);
lean_dec_ref_known(v___x_745_, 3);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_747_, lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_747_, v_msg_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v_ref_747_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
lean_ctor_set(v___x_764_, 3, v___x_763_);
lean_ctor_set(v___x_764_, 4, v___x_762_);
lean_ctor_set(v___x_764_, 5, v___x_762_);
lean_ctor_set(v___x_764_, 6, v___x_762_);
lean_ctor_set(v___x_764_, 7, v___x_762_);
lean_ctor_set(v___x_764_, 8, v___x_762_);
lean_ctor_set(v___x_764_, 9, v___x_762_);
lean_ctor_set(v___x_764_, 10, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(32u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_768_ = ((size_t)5ULL);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_unsigned_to_nat(32u);
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
lean_ctor_set(v___x_773_, 2, v___x_769_);
lean_ctor_set(v___x_773_, 3, v___x_769_);
lean_ctor_set_usize(v___x_773_, 4, v___x_768_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_774_ = lean_box(1);
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
lean_ctor_set(v___x_777_, 2, v___x_774_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_799_, lean_object* v_declHint_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_env_805_; uint8_t v___x_806_; 
v___x_803_ = lean_box(0);
v___x_804_ = lean_st_ref_get(v___y_801_);
v_env_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_804_);
v___x_806_ = l_Lean_Name_isAnonymous(v_declHint_800_);
if (v___x_806_ == 0)
{
uint8_t v_isExporting_807_; 
v_isExporting_807_ = lean_ctor_get_uint8(v_env_805_, sizeof(void*)*13);
if (v_isExporting_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_800_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_msg_799_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
lean_inc_ref(v_env_805_);
v___x_809_ = l_Lean_Environment_setExporting(v_env_805_, v___x_806_);
lean_inc(v_declHint_800_);
lean_inc_ref(v___x_809_);
v___x_810_ = l_Lean_Environment_contains(v___x_809_, v_declHint_800_, v_isExporting_807_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v___x_809_);
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_800_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_msg_799_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_c_817_; lean_object* v___x_818_; 
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_814_ = l_Lean_Options_empty;
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v___x_809_);
lean_ctor_set(v___x_815_, 1, v___x_812_);
lean_ctor_set(v___x_815_, 2, v___x_813_);
lean_ctor_set(v___x_815_, 3, v___x_814_);
lean_inc(v_declHint_800_);
v___x_816_ = l_Lean_MessageData_ofConstName(v_declHint_800_, v___x_806_);
v_c_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_817_, 0, v___x_815_);
lean_ctor_set(v_c_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_805_, v_declHint_800_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_800_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_c_817_);
v___x_821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_MessageData_note(v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v_msg_799_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_860_; 
v_val_826_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_860_ == 0)
{
v___x_828_ = v___x_818_;
v_isShared_829_ = v_isSharedCheck_860_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v___x_818_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_860_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_mod_832_; uint8_t v___x_833_; 
v___x_830_ = l_Lean_Environment_header(v_env_805_);
lean_dec_ref(v_env_805_);
v___x_831_ = l_Lean_EnvironmentHeader_moduleNames(v___x_830_);
v_mod_832_ = lean_array_get(v___x_803_, v___x_831_, v_val_826_);
lean_dec(v_val_826_);
lean_dec_ref(v___x_831_);
v___x_833_ = l_Lean_isPrivateName(v_declHint_800_);
lean_dec(v_declHint_800_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_c_817_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_MessageData_ofName(v_mod_832_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_MessageData_note(v___x_841_);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v_msg_799_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_843_);
v___x_845_ = v___x_828_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_c_817_);
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_MessageData_ofName(v_mod_832_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_MessageData_note(v___x_854_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v_msg_799_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_856_);
v___x_858_ = v___x_828_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_861_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_800_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_msg_799_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_862_, lean_object* v_declHint_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_862_, v_declHint_863_, v___y_864_);
lean_dec(v___y_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_867_, lean_object* v_declHint_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_888_; 
v___x_878_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_867_, v_declHint_868_, v___y_876_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_888_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = l_Lean_unknownIdentifierMessageTag;
v___x_884_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_889_, lean_object* v_declHint_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_889_, v_declHint_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_901_, lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_915_; 
v___x_913_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_902_, v_declHint_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___x_915_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_901_, v_a_914_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_916_, lean_object* v_msg_917_, lean_object* v_declHint_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_916_, v_msg_917_, v_declHint_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v_ref_916_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_935_, lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_946_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_947_ = 0;
lean_inc(v_constName_936_);
v___x_948_ = l_Lean_MessageData_ofConstName(v_constName_936_, v___x_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_935_, v___x_951_, v_constName_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_953_, lean_object* v_constName_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_953_, v_constName_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_ref_953_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_965_, lean_object* v_cs_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_cs_977_; uint8_t v___x_981_; 
v___x_976_ = lean_box(0);
v_cs_977_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_966_, v___x_976_);
v___x_981_ = l_List_isEmpty___redArg(v_cs_977_);
if (v___x_981_ == 0)
{
lean_dec(v_n_965_);
goto v___jp_978_;
}
else
{
lean_object* v_ref_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_cs_977_);
v_ref_982_ = lean_ctor_get(v___y_973_, 2);
v___x_983_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_982_, v_n_965_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
v___jp_978_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_977_, v___x_976_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_992_, lean_object* v_cs_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_992_, v_cs_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = 1;
lean_inc(v_n_1004_);
v___x_1015_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1004_, v___x_1014_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1004_, v_a_1016_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1017_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_n_1004_);
v_a_1018_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1015_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1015_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
if (lean_obj_tag(v_a_1037_) == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_array_to_list(v_a_1038_);
return v___x_1039_;
}
else
{
lean_object* v_head_1040_; 
v_head_1040_ = lean_ctor_get(v_a_1037_, 0);
if (lean_obj_tag(v_head_1040_) == 1)
{
lean_object* v_fields_1041_; 
v_fields_1041_ = lean_ctor_get(v_head_1040_, 1);
if (lean_obj_tag(v_fields_1041_) == 0)
{
lean_object* v_tail_1042_; lean_object* v_n_1043_; lean_object* v___x_1044_; 
lean_inc_ref(v_head_1040_);
v_tail_1042_ = lean_ctor_get(v_a_1037_, 1);
lean_inc(v_tail_1042_);
lean_dec_ref_known(v_a_1037_, 2);
v_n_1043_ = lean_ctor_get(v_head_1040_, 0);
lean_inc(v_n_1043_);
lean_dec_ref_known(v_head_1040_, 2);
v___x_1044_ = lean_array_push(v_a_1038_, v_n_1043_);
v_a_1037_ = v_tail_1042_;
v_a_1038_ = v___x_1044_;
goto _start;
}
else
{
lean_object* v_tail_1046_; 
v_tail_1046_ = lean_ctor_get(v_a_1037_, 1);
lean_inc(v_tail_1046_);
lean_dec_ref_known(v_a_1037_, 2);
v_a_1037_ = v_tail_1046_;
goto _start;
}
}
else
{
lean_object* v_tail_1048_; 
v_tail_1048_ = lean_ctor_get(v_a_1037_, 1);
lean_inc(v_tail_1048_);
lean_dec_ref_known(v_a_1037_, 2);
v_a_1037_ = v_tail_1048_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1056_ = l_Lean_MessageData_ofFormat(v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1057_, lean_object* v_k_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
if (lean_obj_tag(v_stx_1057_) == 3)
{
lean_object* v_val_1068_; lean_object* v_preresolved_1069_; lean_object* v___x_1070_; lean_object* v_pre_1071_; uint8_t v___x_1072_; 
v_val_1068_ = lean_ctor_get(v_stx_1057_, 2);
lean_inc(v_val_1068_);
v_preresolved_1069_ = lean_ctor_get(v_stx_1057_, 3);
v___x_1070_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1069_);
v_pre_1071_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1069_, v___x_1070_);
v___x_1072_ = l_List_isEmpty___redArg(v_pre_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec_ref_known(v_stx_1057_, 4);
lean_dec(v_val_1068_);
lean_dec_ref(v_k_1058_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_pre_1071_);
return v___x_1073_;
}
else
{
lean_object* v_toCold_1074_; lean_object* v_currRecDepth_1075_; lean_object* v_ref_1076_; uint16_t v_optionFlags_1077_; uint8_t v_suppressElabErrors_1078_; uint8_t v_isRecordingDeps_1079_; lean_object* v_ref_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v_pre_1071_);
v_toCold_1074_ = lean_ctor_get(v___y_1065_, 0);
v_currRecDepth_1075_ = lean_ctor_get(v___y_1065_, 1);
v_ref_1076_ = lean_ctor_get(v___y_1065_, 2);
v_optionFlags_1077_ = lean_ctor_get_uint16(v___y_1065_, sizeof(void*)*3);
v_suppressElabErrors_1078_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1079_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 3);
v_ref_1080_ = l_Lean_replaceRef(v_stx_1057_, v_ref_1076_);
lean_dec_ref_known(v_stx_1057_, 4);
lean_inc(v_currRecDepth_1075_);
lean_inc_ref(v_toCold_1074_);
v___x_1081_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1081_, 0, v_toCold_1074_);
lean_ctor_set(v___x_1081_, 1, v_currRecDepth_1075_);
lean_ctor_set(v___x_1081_, 2, v_ref_1080_);
lean_ctor_set_uint16(v___x_1081_, sizeof(void*)*3, v_optionFlags_1077_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3 + 2, v_suppressElabErrors_1078_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3 + 3, v_isRecordingDeps_1079_);
lean_inc(v___y_1066_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
v___x_1082_ = lean_apply_10(v_k_1058_, v_val_1068_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___x_1081_, v___y_1066_, lean_box(0));
return v___x_1082_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_k_1058_);
v___x_1083_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1084_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1057_, v___x_1083_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_stx_1057_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1085_, lean_object* v_k_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1085_, v_k_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1109_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1098_, v___x_1108_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1121_, size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_lt(v_i_1123_, v_sz_1122_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_b_1124_);
return v___x_1135_;
}
else
{
lean_object* v_a_1136_; lean_object* v_name_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1136_ = lean_array_uget_borrowed(v_as_1121_, v_i_1123_);
v_name_1137_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_name_1137_);
v___x_1138_ = l_Lean_mkIdent(v_name_1137_);
lean_inc(v___x_1138_);
v___x_1139_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1138_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1138_, v_a_1140_, v_b_1124_, v___y_1131_);
lean_dec(v_a_1140_);
lean_dec(v___x_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; size_t v___x_1143_; size_t v___x_1144_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = ((size_t)1ULL);
v___x_1144_ = lean_usize_add(v_i_1123_, v___x_1143_);
v_i_1123_ = v___x_1144_;
v_b_1124_ = v_a_1142_;
goto _start;
}
else
{
return v___x_1141_;
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v___x_1138_);
lean_dec_ref(v_b_1124_);
v_a_1146_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1139_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1139_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
size_t v_sz_boxed_1167_; size_t v_i_boxed_1168_; lean_object* v_res_1169_; 
v_sz_boxed_1167_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1168_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1154_, v_sz_boxed_1167_, v_i_boxed_1168_, v_b_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_as_1154_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1189_, lean_object* v_stx_1190_, uint8_t v___x_1191_, lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___f_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
if (v___x_1189_ == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_1205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v_tk_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v_stxForSuggestion_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; uint8_t v___y_1483_; lean_object* v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; uint8_t v___y_1528_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v_stxForExecution_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; uint8_t v___y_1582_; uint8_t v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; uint8_t v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; lean_object* v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; uint8_t v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; uint8_t v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1786_; lean_object* v___y_1787_; uint8_t v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v_argsArray_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; uint8_t v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; uint8_t v___y_1983_; lean_object* v_args_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___x_2005_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2011_; lean_object* v_o_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v_bang_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v_tk_1207_ = l_Lean_Syntax_getArg(v_stx_1190_, v___x_1206_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2064_ = l_Lean_Syntax_getArg(v_stx_1190_, v___x_2005_);
v___x_2065_ = l_Lean_Syntax_isNone(v___x_2064_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
lean_inc(v___x_2064_);
v___x_2066_ = l_Lean_Syntax_matchesNull(v___x_2064_, v___x_2005_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v___x_2064_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2067_;
}
else
{
lean_object* v_bang_2068_; lean_object* v___x_2069_; 
v_bang_2068_ = l_Lean_Syntax_getArg(v___x_2064_, v___x_1206_);
lean_dec(v___x_2064_);
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_bang_2068_);
v_bang_2036_ = v___x_2069_;
v___y_2037_ = v___y_1196_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
goto v___jp_2035_;
}
}
else
{
lean_object* v___x_2070_; 
lean_dec(v___x_2064_);
v___x_2070_ = lean_box(0);
v_bang_2036_ = v___x_2070_;
v___y_2037_ = v___y_1196_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
goto v___jp_2035_;
}
v___jp_1208_:
{
lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(v___x_1191_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1223_, 0, v___y_1211_);
lean_closure_set(v___f_1223_, 1, v___x_1206_);
lean_closure_set(v___f_1223_, 2, v___x_1222_);
lean_closure_set(v___f_1223_, 3, v___y_1221_);
lean_closure_set(v___f_1223_, 4, v___y_1210_);
v___x_1224_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1209_, v___f_1223_, v___y_1217_, v___y_1219_, v___y_1213_, v___y_1216_, v___y_1218_, v___y_1215_, v___y_1220_, v___y_1212_);
lean_dec(v___y_1209_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_usedTheorems_1226_; lean_object* v_diag_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1269_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_usedTheorems_1226_ = lean_ctor_get(v_a_1225_, 0);
v_diag_1227_ = lean_ctor_get(v_a_1225_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1229_ = v_a_1225_;
v_isShared_1230_ = v_isSharedCheck_1269_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_diag_1227_);
lean_inc(v_usedTheorems_1226_);
lean_dec(v_a_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1269_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1214_, v_usedTheorems_1226_, v___y_1218_, v___y_1215_, v___y_1220_, v___y_1212_);
lean_dec_ref(v_usedTheorems_1226_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_ref_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v_ref_1233_ = lean_ctor_get(v___y_1220_, 2);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_a_1232_);
lean_ctor_set(v___x_1229_, 0, v___x_1234_);
v___x_1236_ = v___x_1229_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1232_);
v___x_1236_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
lean_ctor_set(v___x_1238_, 2, v___x_1237_);
lean_ctor_set(v___x_1238_, 3, v___x_1237_);
lean_ctor_set(v___x_1238_, 4, v___x_1237_);
lean_ctor_set(v___x_1238_, 5, v___x_1237_);
lean_inc(v_ref_1233_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_ref_1233_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1241_ = 4;
v___x_1242_ = l_Lean_MessageData_nil;
v___x_1243_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1207_, v___x_1238_, v___x_1239_, v___x_1240_, v___x_1237_, v___x_1241_, v___x_1242_, v___y_1220_, v___y_1212_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1243_, 0);
lean_dec(v_unused_1251_);
v___x_1245_ = v___x_1243_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v___x_1243_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_diag_1227_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_diag_1227_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_diag_1227_);
v_a_1252_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1243_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1243_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_del_object(v___x_1229_);
lean_dec_ref(v_diag_1227_);
lean_dec(v_tk_1207_);
v_a_1261_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1231_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1231_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v___y_1214_);
lean_dec(v_tk_1207_);
v_a_1270_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1224_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1224_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
v___jp_1278_:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = 0;
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1295_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1283_, v___x_1293_, v___y_1281_, v___x_1293_, v___x_1294_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1283_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
if (lean_obj_tag(v___y_1280_) == 0)
{
lean_object* v_ctx_1297_; lean_object* v_simprocs_1298_; lean_object* v_dischargeWrapper_1299_; 
v_ctx_1297_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_ref(v_ctx_1297_);
v_simprocs_1298_ = lean_ctor_get(v_a_1296_, 1);
lean_inc_ref(v_simprocs_1298_);
v_dischargeWrapper_1299_ = lean_ctor_get(v_a_1296_, 2);
lean_inc(v_dischargeWrapper_1299_);
lean_dec(v_a_1296_);
v___y_1209_ = v_dischargeWrapper_1299_;
v___y_1210_ = v_simprocs_1298_;
v___y_1211_ = v___y_1279_;
v___y_1212_ = v___y_1292_;
v___y_1213_ = v___y_1287_;
v___y_1214_ = v_stxForSuggestion_1284_;
v___y_1215_ = v___y_1290_;
v___y_1216_ = v___y_1288_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1286_;
v___y_1220_ = v___y_1291_;
v___y_1221_ = v_ctx_1297_;
goto v___jp_1208_;
}
else
{
lean_dec_ref_known(v___y_1280_, 1);
if (v___y_1282_ == 0)
{
lean_object* v_ctx_1300_; lean_object* v_simprocs_1301_; lean_object* v_dischargeWrapper_1302_; 
v_ctx_1300_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_ref(v_ctx_1300_);
v_simprocs_1301_ = lean_ctor_get(v_a_1296_, 1);
lean_inc_ref(v_simprocs_1301_);
v_dischargeWrapper_1302_ = lean_ctor_get(v_a_1296_, 2);
lean_inc(v_dischargeWrapper_1302_);
lean_dec(v_a_1296_);
v___y_1209_ = v_dischargeWrapper_1302_;
v___y_1210_ = v_simprocs_1301_;
v___y_1211_ = v___y_1279_;
v___y_1212_ = v___y_1292_;
v___y_1213_ = v___y_1287_;
v___y_1214_ = v_stxForSuggestion_1284_;
v___y_1215_ = v___y_1290_;
v___y_1216_ = v___y_1288_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1286_;
v___y_1220_ = v___y_1291_;
v___y_1221_ = v_ctx_1300_;
goto v___jp_1208_;
}
else
{
lean_object* v_ctx_1303_; lean_object* v_simprocs_1304_; lean_object* v_dischargeWrapper_1305_; lean_object* v___x_1306_; 
v_ctx_1303_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_ref(v_ctx_1303_);
v_simprocs_1304_ = lean_ctor_get(v_a_1296_, 1);
lean_inc_ref(v_simprocs_1304_);
v_dischargeWrapper_1305_ = lean_ctor_get(v_a_1296_, 2);
lean_inc(v_dischargeWrapper_1305_);
lean_dec(v_a_1296_);
v___x_1306_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1303_);
v___y_1209_ = v_dischargeWrapper_1305_;
v___y_1210_ = v_simprocs_1304_;
v___y_1211_ = v___y_1279_;
v___y_1212_ = v___y_1292_;
v___y_1213_ = v___y_1287_;
v___y_1214_ = v_stxForSuggestion_1284_;
v___y_1215_ = v___y_1290_;
v___y_1216_ = v___y_1288_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1286_;
v___y_1220_ = v___y_1291_;
v___y_1221_ = v___x_1306_;
goto v___jp_1208_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_stxForSuggestion_1284_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v_tk_1207_);
v_a_1307_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1295_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1295_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc_ref(v___y_1321_);
v___x_1339_ = l_Array_append___redArg(v___y_1321_, v___y_1338_);
lean_dec_ref(v___y_1338_);
lean_inc(v___y_1323_);
lean_inc(v___y_1328_);
v___x_1340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1340_, 0, v___y_1328_);
lean_ctor_set(v___x_1340_, 1, v___y_1323_);
lean_ctor_set(v___x_1340_, 2, v___x_1339_);
v___x_1341_ = l_Lean_Syntax_node6(v___y_1328_, v___y_1317_, v___y_1319_, v___y_1330_, v___y_1333_, v___y_1331_, v___y_1320_, v___x_1340_);
v___y_1279_ = v___y_1316_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1322_;
v___y_1282_ = v___y_1324_;
v___y_1283_ = v___y_1336_;
v_stxForSuggestion_1284_ = v___x_1341_;
v___y_1285_ = v___y_1329_;
v___y_1286_ = v___y_1318_;
v___y_1287_ = v___y_1326_;
v___y_1288_ = v___y_1337_;
v___y_1289_ = v___y_1335_;
v___y_1290_ = v___y_1334_;
v___y_1291_ = v___y_1327_;
v___y_1292_ = v___y_1325_;
goto v___jp_1278_;
}
v___jp_1342_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc_ref_n(v___y_1347_, 2);
v___x_1366_ = l_Array_append___redArg(v___y_1347_, v___y_1365_);
lean_dec_ref(v___y_1365_);
lean_inc_n(v___y_1348_, 3);
lean_inc_n(v___y_1355_, 5);
v___x_1367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1367_, 0, v___y_1355_);
lean_ctor_set(v___x_1367_, 1, v___y_1348_);
lean_ctor_set(v___x_1367_, 2, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___y_1355_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1371_ = l_Lean_Syntax_SepArray_ofElems(v___x_1370_, v___y_1357_);
lean_dec_ref(v___y_1357_);
v___x_1372_ = l_Array_append___redArg(v___y_1347_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1355_);
lean_ctor_set(v___x_1373_, 1, v___y_1348_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1355_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_Syntax_node3(v___y_1355_, v___y_1348_, v___x_1369_, v___x_1373_, v___x_1375_);
if (lean_obj_tag(v___y_1350_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; 
v_val_1377_ = lean_ctor_get(v___y_1350_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___y_1350_, 1);
v___x_1378_ = l_Array_mkArray1___redArg(v_val_1377_);
v___y_1316_ = v___y_1343_;
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___x_1376_;
v___y_1321_ = v___y_1347_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1353_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___y_1355_;
v___y_1329_ = v___y_1356_;
v___y_1330_ = v___y_1358_;
v___y_1331_ = v___x_1367_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___x_1378_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1379_; 
lean_dec(v___y_1350_);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1316_ = v___y_1343_;
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___x_1376_;
v___y_1321_ = v___y_1347_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1353_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___y_1355_;
v___y_1329_ = v___y_1356_;
v___y_1330_ = v___y_1358_;
v___y_1331_ = v___x_1367_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___x_1379_;
goto v___jp_1315_;
}
}
v___jp_1380_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v___y_1386_);
v___x_1404_ = l_Array_append___redArg(v___y_1386_, v___y_1403_);
lean_dec_ref(v___y_1403_);
lean_inc(v___y_1387_);
lean_inc(v___y_1394_);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1394_);
lean_ctor_set(v___x_1405_, 1, v___y_1387_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
if (lean_obj_tag(v___y_1383_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_val_1406_ = lean_ctor_get(v___y_1383_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v___y_1383_, 1);
v___x_1407_ = l_Lean_SourceInfo_fromRef(v_val_1406_, v___x_1191_);
lean_dec(v_val_1406_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Array_mkArray1___redArg(v___x_1409_);
v___y_1343_ = v___y_1381_;
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1384_;
v___y_1346_ = v___y_1385_;
v___y_1347_ = v___y_1386_;
v___y_1348_ = v___y_1387_;
v___y_1349_ = v___y_1388_;
v___y_1350_ = v___y_1389_;
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___y_1391_;
v___y_1353_ = v___y_1392_;
v___y_1354_ = v___y_1393_;
v___y_1355_ = v___y_1394_;
v___y_1356_ = v___y_1395_;
v___y_1357_ = v___y_1396_;
v___y_1358_ = v___y_1397_;
v___y_1359_ = v___y_1398_;
v___y_1360_ = v___x_1405_;
v___y_1361_ = v___y_1400_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1402_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___x_1410_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v___y_1383_);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1343_ = v___y_1381_;
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1384_;
v___y_1346_ = v___y_1385_;
v___y_1347_ = v___y_1386_;
v___y_1348_ = v___y_1387_;
v___y_1349_ = v___y_1388_;
v___y_1350_ = v___y_1389_;
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___y_1391_;
v___y_1353_ = v___y_1392_;
v___y_1354_ = v___y_1393_;
v___y_1355_ = v___y_1394_;
v___y_1356_ = v___y_1395_;
v___y_1357_ = v___y_1396_;
v___y_1358_ = v___y_1397_;
v___y_1359_ = v___y_1398_;
v___y_1360_ = v___x_1405_;
v___y_1361_ = v___y_1400_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1402_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___x_1411_;
goto v___jp_1342_;
}
}
v___jp_1412_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_inc_ref(v___y_1425_);
v___x_1436_ = l_Array_append___redArg(v___y_1425_, v___y_1435_);
lean_dec_ref(v___y_1435_);
lean_inc(v___y_1427_);
lean_inc(v___y_1414_);
v___x_1437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1414_);
lean_ctor_set(v___x_1437_, 1, v___y_1427_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
v___x_1438_ = l_Lean_Syntax_node6(v___y_1414_, v___y_1418_, v___y_1424_, v___y_1428_, v___y_1432_, v___y_1417_, v___y_1415_, v___x_1437_);
v___y_1279_ = v___y_1413_;
v___y_1280_ = v___y_1429_;
v___y_1281_ = v___y_1419_;
v___y_1282_ = v___y_1420_;
v___y_1283_ = v___y_1433_;
v_stxForSuggestion_1284_ = v___x_1438_;
v___y_1285_ = v___y_1426_;
v___y_1286_ = v___y_1416_;
v___y_1287_ = v___y_1422_;
v___y_1288_ = v___y_1434_;
v___y_1289_ = v___y_1431_;
v___y_1290_ = v___y_1430_;
v___y_1291_ = v___y_1423_;
v___y_1292_ = v___y_1421_;
goto v___jp_1278_;
}
v___jp_1439_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref_n(v___y_1451_, 2);
v___x_1463_ = l_Array_append___redArg(v___y_1451_, v___y_1462_);
lean_dec_ref(v___y_1462_);
lean_inc_n(v___y_1455_, 3);
lean_inc_n(v___y_1441_, 5);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1441_);
lean_ctor_set(v___x_1464_, 1, v___y_1455_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1441_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1468_ = l_Lean_Syntax_SepArray_ofElems(v___x_1467_, v___y_1453_);
lean_dec_ref(v___y_1453_);
v___x_1469_ = l_Array_append___redArg(v___y_1451_, v___x_1468_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1441_);
lean_ctor_set(v___x_1470_, 1, v___y_1455_);
lean_ctor_set(v___x_1470_, 2, v___x_1469_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1441_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node3(v___y_1441_, v___y_1455_, v___x_1466_, v___x_1470_, v___x_1472_);
if (lean_obj_tag(v___y_1445_) == 1)
{
lean_object* v_val_1474_; lean_object* v___x_1475_; 
v_val_1474_ = lean_ctor_get(v___y_1445_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v___y_1445_, 1);
v___x_1475_ = l_Array_mkArray1___redArg(v_val_1474_);
v___y_1413_ = v___y_1440_;
v___y_1414_ = v___y_1441_;
v___y_1415_ = v___x_1473_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___x_1464_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1446_;
v___y_1421_ = v___y_1447_;
v___y_1422_ = v___y_1448_;
v___y_1423_ = v___y_1449_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1451_;
v___y_1426_ = v___y_1452_;
v___y_1427_ = v___y_1455_;
v___y_1428_ = v___y_1454_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1459_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v___y_1460_;
v___y_1435_ = v___x_1475_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1476_; 
lean_dec(v___y_1445_);
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1413_ = v___y_1440_;
v___y_1414_ = v___y_1441_;
v___y_1415_ = v___x_1473_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___x_1464_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1446_;
v___y_1421_ = v___y_1447_;
v___y_1422_ = v___y_1448_;
v___y_1423_ = v___y_1449_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1451_;
v___y_1426_ = v___y_1452_;
v___y_1427_ = v___y_1455_;
v___y_1428_ = v___y_1454_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1459_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v___y_1460_;
v___y_1435_ = v___x_1476_;
goto v___jp_1412_;
}
}
v___jp_1477_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_inc_ref(v___y_1490_);
v___x_1501_ = l_Array_append___redArg(v___y_1490_, v___y_1500_);
lean_dec_ref(v___y_1500_);
lean_inc(v___y_1494_);
lean_inc(v___y_1479_);
v___x_1502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1479_);
lean_ctor_set(v___x_1502_, 1, v___y_1494_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
if (lean_obj_tag(v___y_1480_) == 1)
{
lean_object* v_val_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_val_1503_ = lean_ctor_get(v___y_1480_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v___y_1480_, 1);
v___x_1504_ = l_Lean_SourceInfo_fromRef(v_val_1503_, v___x_1191_);
lean_dec(v_val_1503_);
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Array_mkArray1___redArg(v___x_1506_);
v___y_1440_ = v___y_1478_;
v___y_1441_ = v___y_1479_;
v___y_1442_ = v___y_1481_;
v___y_1443_ = v___y_1482_;
v___y_1444_ = v___y_1483_;
v___y_1445_ = v___y_1484_;
v___y_1446_ = v___y_1485_;
v___y_1447_ = v___y_1486_;
v___y_1448_ = v___y_1487_;
v___y_1449_ = v___y_1488_;
v___y_1450_ = v___y_1489_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1497_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___x_1502_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1498_;
v___y_1462_ = v___x_1507_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1508_; 
lean_dec(v___y_1480_);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1440_ = v___y_1478_;
v___y_1441_ = v___y_1479_;
v___y_1442_ = v___y_1481_;
v___y_1443_ = v___y_1482_;
v___y_1444_ = v___y_1483_;
v___y_1445_ = v___y_1484_;
v___y_1446_ = v___y_1485_;
v___y_1447_ = v___y_1486_;
v___y_1448_ = v___y_1487_;
v___y_1449_ = v___y_1488_;
v___y_1450_ = v___y_1489_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1497_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___x_1502_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1498_;
v___y_1462_ = v___x_1508_;
goto v___jp_1439_;
}
}
v___jp_1509_:
{
lean_object* v_ref_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_ref_1529_ = lean_ctor_get(v___y_1519_, 2);
v___x_1530_ = l_Lean_SourceInfo_fromRef(v_ref_1529_, v___y_1528_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1532_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1531_);
v___x_1533_ = l_Lean_SourceInfo_fromRef(v_tk_1207_, v___x_1191_);
v___x_1534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
v___x_1535_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1536_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1513_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1538_; 
v_val_1537_ = lean_ctor_get(v___y_1513_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___y_1513_, 1);
v___x_1538_ = l_Array_mkArray1___redArg(v_val_1537_);
v___y_1478_ = v___y_1510_;
v___y_1479_ = v___x_1530_;
v___y_1480_ = v___y_1511_;
v___y_1481_ = v___y_1512_;
v___y_1482_ = v___x_1532_;
v___y_1483_ = v___y_1514_;
v___y_1484_ = v___y_1515_;
v___y_1485_ = v___y_1516_;
v___y_1486_ = v___y_1517_;
v___y_1487_ = v___y_1518_;
v___y_1488_ = v___y_1519_;
v___y_1489_ = v___x_1534_;
v___y_1490_ = v___x_1536_;
v___y_1491_ = v___y_1520_;
v___y_1492_ = v___y_1521_;
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___x_1535_;
v___y_1495_ = v___y_1523_;
v___y_1496_ = v___y_1525_;
v___y_1497_ = v___y_1524_;
v___y_1498_ = v___y_1527_;
v___y_1499_ = v___y_1526_;
v___y_1500_ = v___x_1538_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1539_; 
lean_dec(v___y_1513_);
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1478_ = v___y_1510_;
v___y_1479_ = v___x_1530_;
v___y_1480_ = v___y_1511_;
v___y_1481_ = v___y_1512_;
v___y_1482_ = v___x_1532_;
v___y_1483_ = v___y_1514_;
v___y_1484_ = v___y_1515_;
v___y_1485_ = v___y_1516_;
v___y_1486_ = v___y_1517_;
v___y_1487_ = v___y_1518_;
v___y_1488_ = v___y_1519_;
v___y_1489_ = v___x_1534_;
v___y_1490_ = v___x_1536_;
v___y_1491_ = v___y_1520_;
v___y_1492_ = v___y_1521_;
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___x_1535_;
v___y_1495_ = v___y_1523_;
v___y_1496_ = v___y_1525_;
v___y_1497_ = v___y_1524_;
v___y_1498_ = v___y_1527_;
v___y_1499_ = v___y_1526_;
v___y_1500_ = v___x_1539_;
goto v___jp_1477_;
}
}
v___jp_1540_:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1542_);
if (lean_obj_tag(v___y_1545_) == 0)
{
lean_object* v_a_1560_; uint8_t v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = 0;
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1543_;
v___y_1512_ = v___y_1552_;
v___y_1513_ = v___y_1546_;
v___y_1514_ = v___y_1547_;
v___y_1515_ = v___y_1548_;
v___y_1516_ = v___y_1549_;
v___y_1517_ = v___y_1558_;
v___y_1518_ = v___y_1553_;
v___y_1519_ = v___y_1557_;
v___y_1520_ = v___y_1551_;
v___y_1521_ = v___y_1544_;
v___y_1522_ = v_a_1560_;
v___y_1523_ = v___y_1545_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v___y_1556_;
v___y_1526_ = v___y_1554_;
v___y_1527_ = v_stxForExecution_1550_;
v___y_1528_ = v___x_1561_;
goto v___jp_1509_;
}
else
{
if (v___y_1549_ == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1559_);
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1543_;
v___y_1512_ = v___y_1552_;
v___y_1513_ = v___y_1546_;
v___y_1514_ = v___y_1547_;
v___y_1515_ = v___y_1548_;
v___y_1516_ = v___y_1549_;
v___y_1517_ = v___y_1558_;
v___y_1518_ = v___y_1553_;
v___y_1519_ = v___y_1557_;
v___y_1520_ = v___y_1551_;
v___y_1521_ = v___y_1544_;
v___y_1522_ = v_a_1562_;
v___y_1523_ = v___y_1545_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v___y_1556_;
v___y_1526_ = v___y_1554_;
v___y_1527_ = v_stxForExecution_1550_;
v___y_1528_ = v___y_1549_;
goto v___jp_1509_;
}
else
{
lean_object* v_a_1563_; lean_object* v_ref_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1563_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1559_);
v_ref_1564_ = lean_ctor_get(v___y_1557_, 2);
v___x_1565_ = 0;
v___x_1566_ = l_Lean_SourceInfo_fromRef(v_ref_1564_, v___x_1565_);
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1568_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1567_);
v___x_1569_ = l_Lean_SourceInfo_fromRef(v_tk_1207_, v___x_1191_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1573_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1546_) == 1)
{
lean_object* v_val_1574_; lean_object* v___x_1575_; 
v_val_1574_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v___y_1546_, 1);
v___x_1575_ = l_Array_mkArray1___redArg(v_val_1574_);
v___y_1381_ = v___y_1541_;
v___y_1382_ = v___x_1568_;
v___y_1383_ = v___y_1543_;
v___y_1384_ = v___y_1552_;
v___y_1385_ = v___x_1571_;
v___y_1386_ = v___x_1573_;
v___y_1387_ = v___x_1572_;
v___y_1388_ = v___y_1547_;
v___y_1389_ = v___y_1548_;
v___y_1390_ = v___y_1549_;
v___y_1391_ = v___y_1558_;
v___y_1392_ = v___y_1553_;
v___y_1393_ = v___y_1557_;
v___y_1394_ = v___x_1566_;
v___y_1395_ = v___y_1551_;
v___y_1396_ = v___y_1544_;
v___y_1397_ = v_a_1563_;
v___y_1398_ = v___y_1545_;
v___y_1399_ = v___y_1556_;
v___y_1400_ = v___y_1555_;
v___y_1401_ = v_stxForExecution_1550_;
v___y_1402_ = v___y_1554_;
v___y_1403_ = v___x_1575_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1576_; 
lean_dec(v___y_1546_);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1381_ = v___y_1541_;
v___y_1382_ = v___x_1568_;
v___y_1383_ = v___y_1543_;
v___y_1384_ = v___y_1552_;
v___y_1385_ = v___x_1571_;
v___y_1386_ = v___x_1573_;
v___y_1387_ = v___x_1572_;
v___y_1388_ = v___y_1547_;
v___y_1389_ = v___y_1548_;
v___y_1390_ = v___y_1549_;
v___y_1391_ = v___y_1558_;
v___y_1392_ = v___y_1553_;
v___y_1393_ = v___y_1557_;
v___y_1394_ = v___x_1566_;
v___y_1395_ = v___y_1551_;
v___y_1396_ = v___y_1544_;
v___y_1397_ = v_a_1563_;
v___y_1398_ = v___y_1545_;
v___y_1399_ = v___y_1556_;
v___y_1400_ = v___y_1555_;
v___y_1401_ = v_stxForExecution_1550_;
v___y_1402_ = v___y_1554_;
v___y_1403_ = v___x_1576_;
goto v___jp_1380_;
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_inc_ref(v___y_1587_);
v___x_1604_ = l_Array_append___redArg(v___y_1587_, v___y_1603_);
lean_dec_ref(v___y_1603_);
lean_inc(v___y_1595_);
lean_inc(v___y_1599_);
v___x_1605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1599_);
lean_ctor_set(v___x_1605_, 1, v___y_1595_);
lean_ctor_set(v___x_1605_, 2, v___x_1604_);
lean_inc(v___y_1584_);
v___x_1606_ = l_Lean_Syntax_node6(v___y_1599_, v___y_1580_, v___y_1586_, v___y_1584_, v___y_1593_, v___y_1592_, v___y_1588_, v___x_1605_);
v___y_1541_ = v___y_1578_;
v___y_1542_ = v___y_1584_;
v___y_1543_ = v___y_1594_;
v___y_1544_ = v___y_1590_;
v___y_1545_ = v___y_1591_;
v___y_1546_ = v___y_1581_;
v___y_1547_ = v___y_1582_;
v___y_1548_ = v___y_1598_;
v___y_1549_ = v___y_1583_;
v_stxForExecution_1550_ = v___x_1606_;
v___y_1551_ = v___y_1589_;
v___y_1552_ = v___y_1600_;
v___y_1553_ = v___y_1585_;
v___y_1554_ = v___y_1579_;
v___y_1555_ = v___y_1602_;
v___y_1556_ = v___y_1601_;
v___y_1557_ = v___y_1596_;
v___y_1558_ = v___y_1597_;
goto v___jp_1540_;
}
v___jp_1607_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_inc_ref_n(v___y_1624_, 2);
v___x_1632_ = l_Array_append___redArg(v___y_1624_, v___y_1631_);
lean_dec_ref(v___y_1631_);
lean_inc_n(v___y_1614_, 3);
lean_inc_n(v___y_1620_, 5);
v___x_1633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1633_, 0, v___y_1620_);
lean_ctor_set(v___x_1633_, 1, v___y_1614_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1620_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1637_ = l_Lean_Syntax_SepArray_ofElems(v___x_1636_, v___y_1625_);
v___x_1638_ = l_Array_append___redArg(v___y_1624_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1620_);
lean_ctor_set(v___x_1639_, 1, v___y_1614_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1620_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_Syntax_node3(v___y_1620_, v___y_1614_, v___x_1635_, v___x_1639_, v___x_1641_);
if (lean_obj_tag(v___y_1618_) == 1)
{
lean_object* v_val_1643_; lean_object* v___x_1644_; 
v_val_1643_ = lean_ctor_get(v___y_1618_, 0);
lean_inc(v_val_1643_);
v___x_1644_ = l_Array_mkArray1___redArg(v_val_1643_);
v___y_1578_ = v___y_1608_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1616_;
v___y_1582_ = v___y_1617_;
v___y_1583_ = v___y_1619_;
v___y_1584_ = v___y_1621_;
v___y_1585_ = v___y_1622_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___y_1624_;
v___y_1588_ = v___x_1642_;
v___y_1589_ = v___y_1626_;
v___y_1590_ = v___y_1625_;
v___y_1591_ = v___y_1627_;
v___y_1592_ = v___x_1633_;
v___y_1593_ = v___y_1609_;
v___y_1594_ = v___y_1610_;
v___y_1595_ = v___y_1614_;
v___y_1596_ = v___y_1613_;
v___y_1597_ = v___y_1615_;
v___y_1598_ = v___y_1618_;
v___y_1599_ = v___y_1620_;
v___y_1600_ = v___y_1629_;
v___y_1601_ = v___y_1628_;
v___y_1602_ = v___y_1630_;
v___y_1603_ = v___x_1644_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1645_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1578_ = v___y_1608_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1616_;
v___y_1582_ = v___y_1617_;
v___y_1583_ = v___y_1619_;
v___y_1584_ = v___y_1621_;
v___y_1585_ = v___y_1622_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___y_1624_;
v___y_1588_ = v___x_1642_;
v___y_1589_ = v___y_1626_;
v___y_1590_ = v___y_1625_;
v___y_1591_ = v___y_1627_;
v___y_1592_ = v___x_1633_;
v___y_1593_ = v___y_1609_;
v___y_1594_ = v___y_1610_;
v___y_1595_ = v___y_1614_;
v___y_1596_ = v___y_1613_;
v___y_1597_ = v___y_1615_;
v___y_1598_ = v___y_1618_;
v___y_1599_ = v___y_1620_;
v___y_1600_ = v___y_1629_;
v___y_1601_ = v___y_1628_;
v___y_1602_ = v___y_1630_;
v___y_1603_ = v___x_1645_;
goto v___jp_1577_;
}
}
v___jp_1646_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_inc_ref(v___y_1662_);
v___x_1670_ = l_Array_append___redArg(v___y_1662_, v___y_1669_);
lean_dec_ref(v___y_1669_);
lean_inc(v___y_1651_);
lean_inc(v___y_1658_);
v___x_1671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1658_);
lean_ctor_set(v___x_1671_, 1, v___y_1651_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
if (lean_obj_tag(v___y_1648_) == 1)
{
lean_object* v_val_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_val_1672_ = lean_ctor_get(v___y_1648_, 0);
v___x_1673_ = l_Lean_SourceInfo_fromRef(v_val_1672_, v___x_1191_);
v___x_1674_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Array_mkArray1___redArg(v___x_1675_);
v___y_1608_ = v___y_1647_;
v___y_1609_ = v___x_1671_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1649_;
v___y_1612_ = v___y_1650_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1651_;
v___y_1615_ = v___y_1653_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1655_;
v___y_1618_ = v___y_1656_;
v___y_1619_ = v___y_1657_;
v___y_1620_ = v___y_1658_;
v___y_1621_ = v___y_1659_;
v___y_1622_ = v___y_1660_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1662_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1663_;
v___y_1627_ = v___y_1665_;
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1666_;
v___y_1630_ = v___y_1668_;
v___y_1631_ = v___x_1676_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1608_ = v___y_1647_;
v___y_1609_ = v___x_1671_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1649_;
v___y_1612_ = v___y_1650_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1651_;
v___y_1615_ = v___y_1653_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1655_;
v___y_1618_ = v___y_1656_;
v___y_1619_ = v___y_1657_;
v___y_1620_ = v___y_1658_;
v___y_1621_ = v___y_1659_;
v___y_1622_ = v___y_1660_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1662_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1663_;
v___y_1627_ = v___y_1665_;
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1666_;
v___y_1630_ = v___y_1668_;
v___y_1631_ = v___x_1677_;
goto v___jp_1607_;
}
}
v___jp_1678_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_inc_ref(v___y_1682_);
v___x_1705_ = l_Array_append___redArg(v___y_1682_, v___y_1704_);
lean_dec_ref(v___y_1704_);
lean_inc(v___y_1692_);
lean_inc(v___y_1685_);
v___x_1706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1706_, 0, v___y_1685_);
lean_ctor_set(v___x_1706_, 1, v___y_1692_);
lean_ctor_set(v___x_1706_, 2, v___x_1705_);
lean_inc(v___y_1688_);
v___x_1707_ = l_Lean_Syntax_node6(v___y_1685_, v___y_1694_, v___y_1700_, v___y_1688_, v___y_1696_, v___y_1681_, v___y_1687_, v___x_1706_);
v___y_1541_ = v___y_1679_;
v___y_1542_ = v___y_1688_;
v___y_1543_ = v___y_1695_;
v___y_1544_ = v___y_1691_;
v___y_1545_ = v___y_1693_;
v___y_1546_ = v___y_1683_;
v___y_1547_ = v___y_1684_;
v___y_1548_ = v___y_1699_;
v___y_1549_ = v___y_1686_;
v_stxForExecution_1550_ = v___x_1707_;
v___y_1551_ = v___y_1690_;
v___y_1552_ = v___y_1701_;
v___y_1553_ = v___y_1689_;
v___y_1554_ = v___y_1680_;
v___y_1555_ = v___y_1703_;
v___y_1556_ = v___y_1702_;
v___y_1557_ = v___y_1697_;
v___y_1558_ = v___y_1698_;
goto v___jp_1540_;
}
v___jp_1708_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc_ref_n(v___y_1714_, 2);
v___x_1733_ = l_Array_append___redArg(v___y_1714_, v___y_1732_);
lean_dec_ref(v___y_1732_);
lean_inc_n(v___y_1725_, 3);
lean_inc_n(v___y_1719_, 5);
v___x_1734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1734_, 0, v___y_1719_);
lean_ctor_set(v___x_1734_, 1, v___y_1725_);
lean_ctor_set(v___x_1734_, 2, v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1719_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1738_ = l_Lean_Syntax_SepArray_ofElems(v___x_1737_, v___y_1723_);
v___x_1739_ = l_Array_append___redArg(v___y_1714_, v___x_1738_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1719_);
lean_ctor_set(v___x_1740_, 1, v___y_1725_);
lean_ctor_set(v___x_1740_, 2, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1719_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = l_Lean_Syntax_node3(v___y_1719_, v___y_1725_, v___x_1736_, v___x_1740_, v___x_1742_);
if (lean_obj_tag(v___y_1718_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1745_; 
v_val_1744_ = lean_ctor_get(v___y_1718_, 0);
lean_inc(v_val_1744_);
v___x_1745_ = l_Array_mkArray1___redArg(v_val_1744_);
v___y_1679_ = v___y_1709_;
v___y_1680_ = v___y_1711_;
v___y_1681_ = v___x_1734_;
v___y_1682_ = v___y_1714_;
v___y_1683_ = v___y_1716_;
v___y_1684_ = v___y_1717_;
v___y_1685_ = v___y_1719_;
v___y_1686_ = v___y_1720_;
v___y_1687_ = v___x_1743_;
v___y_1688_ = v___y_1721_;
v___y_1689_ = v___y_1722_;
v___y_1690_ = v___y_1724_;
v___y_1691_ = v___y_1723_;
v___y_1692_ = v___y_1725_;
v___y_1693_ = v___y_1726_;
v___y_1694_ = v___y_1730_;
v___y_1695_ = v___y_1710_;
v___y_1696_ = v___y_1712_;
v___y_1697_ = v___y_1713_;
v___y_1698_ = v___y_1715_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1727_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___y_1728_;
v___y_1703_ = v___y_1731_;
v___y_1704_ = v___x_1745_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1679_ = v___y_1709_;
v___y_1680_ = v___y_1711_;
v___y_1681_ = v___x_1734_;
v___y_1682_ = v___y_1714_;
v___y_1683_ = v___y_1716_;
v___y_1684_ = v___y_1717_;
v___y_1685_ = v___y_1719_;
v___y_1686_ = v___y_1720_;
v___y_1687_ = v___x_1743_;
v___y_1688_ = v___y_1721_;
v___y_1689_ = v___y_1722_;
v___y_1690_ = v___y_1724_;
v___y_1691_ = v___y_1723_;
v___y_1692_ = v___y_1725_;
v___y_1693_ = v___y_1726_;
v___y_1694_ = v___y_1730_;
v___y_1695_ = v___y_1710_;
v___y_1696_ = v___y_1712_;
v___y_1697_ = v___y_1713_;
v___y_1698_ = v___y_1715_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1727_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___y_1728_;
v___y_1703_ = v___y_1731_;
v___y_1704_ = v___x_1746_;
goto v___jp_1678_;
}
}
v___jp_1747_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_inc_ref(v___y_1752_);
v___x_1771_ = l_Array_append___redArg(v___y_1752_, v___y_1770_);
lean_dec_ref(v___y_1770_);
lean_inc(v___y_1764_);
lean_inc(v___y_1757_);
v___x_1772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1772_, 0, v___y_1757_);
lean_ctor_set(v___x_1772_, 1, v___y_1764_);
lean_ctor_set(v___x_1772_, 2, v___x_1771_);
if (lean_obj_tag(v___y_1749_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_val_1773_ = lean_ctor_get(v___y_1749_, 0);
v___x_1774_ = l_Lean_SourceInfo_fromRef(v_val_1773_, v___x_1191_);
v___x_1775_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Array_mkArray1___redArg(v___x_1776_);
v___y_1709_ = v___y_1748_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___x_1772_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1752_;
v___y_1715_ = v___y_1753_;
v___y_1716_ = v___y_1754_;
v___y_1717_ = v___y_1755_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1758_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1760_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1761_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___y_1763_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1768_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1766_;
v___y_1731_ = v___y_1769_;
v___y_1732_ = v___x_1777_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1709_ = v___y_1748_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___x_1772_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1752_;
v___y_1715_ = v___y_1753_;
v___y_1716_ = v___y_1754_;
v___y_1717_ = v___y_1755_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1758_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1760_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1761_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___y_1763_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1768_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1766_;
v___y_1731_ = v___y_1769_;
v___y_1732_ = v___x_1778_;
goto v___jp_1708_;
}
}
v___jp_1779_:
{
lean_object* v_ref_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_ref_1798_ = lean_ctor_get(v___y_1783_, 2);
v___x_1799_ = l_Lean_SourceInfo_fromRef(v_ref_1798_, v___y_1797_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
lean_inc_ref(v___x_1192_);
v___x_1801_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1800_);
v___x_1802_ = l_Lean_SourceInfo_fromRef(v_tk_1207_, v___x_1191_);
v___x_1803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1800_);
v___x_1804_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1805_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1785_) == 1)
{
lean_object* v_val_1806_; lean_object* v___x_1807_; 
v_val_1806_ = lean_ctor_get(v___y_1785_, 0);
lean_inc(v_val_1806_);
v___x_1807_ = l_Array_mkArray1___redArg(v_val_1806_);
v___y_1748_ = v___y_1780_;
v___y_1749_ = v___y_1781_;
v___y_1750_ = v___y_1782_;
v___y_1751_ = v___y_1783_;
v___y_1752_ = v___x_1805_;
v___y_1753_ = v___y_1784_;
v___y_1754_ = v___y_1785_;
v___y_1755_ = v___y_1786_;
v___y_1756_ = v___y_1787_;
v___y_1757_ = v___x_1799_;
v___y_1758_ = v___y_1788_;
v___y_1759_ = v___y_1789_;
v___y_1760_ = v___y_1790_;
v___y_1761_ = v___y_1791_;
v___y_1762_ = v___y_1792_;
v___y_1763_ = v___y_1793_;
v___y_1764_ = v___x_1804_;
v___y_1765_ = v___x_1803_;
v___y_1766_ = v___x_1801_;
v___y_1767_ = v___y_1795_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___y_1796_;
v___y_1770_ = v___x_1807_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1748_ = v___y_1780_;
v___y_1749_ = v___y_1781_;
v___y_1750_ = v___y_1782_;
v___y_1751_ = v___y_1783_;
v___y_1752_ = v___x_1805_;
v___y_1753_ = v___y_1784_;
v___y_1754_ = v___y_1785_;
v___y_1755_ = v___y_1786_;
v___y_1756_ = v___y_1787_;
v___y_1757_ = v___x_1799_;
v___y_1758_ = v___y_1788_;
v___y_1759_ = v___y_1789_;
v___y_1760_ = v___y_1790_;
v___y_1761_ = v___y_1791_;
v___y_1762_ = v___y_1792_;
v___y_1763_ = v___y_1793_;
v___y_1764_ = v___x_1804_;
v___y_1765_ = v___x_1803_;
v___y_1766_ = v___x_1801_;
v___y_1767_ = v___y_1795_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___y_1796_;
v___y_1770_ = v___x_1808_;
goto v___jp_1747_;
}
}
v___jp_1809_:
{
if (lean_obj_tag(v___y_1813_) == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = 0;
v___y_1780_ = v___y_1810_;
v___y_1781_ = v___y_1812_;
v___y_1782_ = v___y_1822_;
v___y_1783_ = v___y_1825_;
v___y_1784_ = v___y_1826_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1816_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___y_1811_;
v___y_1790_ = v___y_1821_;
v___y_1791_ = v___y_1819_;
v___y_1792_ = v_argsArray_1818_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1824_;
v___y_1795_ = v___y_1820_;
v___y_1796_ = v___y_1823_;
v___y_1797_ = v___x_1827_;
goto v___jp_1779_;
}
else
{
if (v___y_1817_ == 0)
{
v___y_1780_ = v___y_1810_;
v___y_1781_ = v___y_1812_;
v___y_1782_ = v___y_1822_;
v___y_1783_ = v___y_1825_;
v___y_1784_ = v___y_1826_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1816_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___y_1811_;
v___y_1790_ = v___y_1821_;
v___y_1791_ = v___y_1819_;
v___y_1792_ = v_argsArray_1818_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1824_;
v___y_1795_ = v___y_1820_;
v___y_1796_ = v___y_1823_;
v___y_1797_ = v___y_1817_;
goto v___jp_1779_;
}
else
{
lean_object* v_ref_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_ref_1828_ = lean_ctor_get(v___y_1825_, 2);
v___x_1829_ = 0;
v___x_1830_ = l_Lean_SourceInfo_fromRef(v_ref_1828_, v___x_1829_);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
lean_inc_ref(v___x_1192_);
v___x_1832_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1831_);
v___x_1833_ = l_Lean_SourceInfo_fromRef(v_tk_1207_, v___x_1191_);
v___x_1834_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1837_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1815_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1839_; 
v_val_1838_ = lean_ctor_get(v___y_1815_, 0);
lean_inc(v_val_1838_);
v___x_1839_ = l_Array_mkArray1___redArg(v_val_1838_);
v___y_1647_ = v___y_1810_;
v___y_1648_ = v___y_1812_;
v___y_1649_ = v___y_1822_;
v___y_1650_ = v___x_1832_;
v___y_1651_ = v___x_1836_;
v___y_1652_ = v___y_1825_;
v___y_1653_ = v___y_1826_;
v___y_1654_ = v___y_1815_;
v___y_1655_ = v___y_1814_;
v___y_1656_ = v___y_1816_;
v___y_1657_ = v___y_1817_;
v___y_1658_ = v___x_1830_;
v___y_1659_ = v___y_1811_;
v___y_1660_ = v___y_1821_;
v___y_1661_ = v___x_1835_;
v___y_1662_ = v___x_1837_;
v___y_1663_ = v___y_1819_;
v___y_1664_ = v_argsArray_1818_;
v___y_1665_ = v___y_1813_;
v___y_1666_ = v___y_1820_;
v___y_1667_ = v___y_1824_;
v___y_1668_ = v___y_1823_;
v___y_1669_ = v___x_1839_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1647_ = v___y_1810_;
v___y_1648_ = v___y_1812_;
v___y_1649_ = v___y_1822_;
v___y_1650_ = v___x_1832_;
v___y_1651_ = v___x_1836_;
v___y_1652_ = v___y_1825_;
v___y_1653_ = v___y_1826_;
v___y_1654_ = v___y_1815_;
v___y_1655_ = v___y_1814_;
v___y_1656_ = v___y_1816_;
v___y_1657_ = v___y_1817_;
v___y_1658_ = v___x_1830_;
v___y_1659_ = v___y_1811_;
v___y_1660_ = v___y_1821_;
v___y_1661_ = v___x_1835_;
v___y_1662_ = v___x_1837_;
v___y_1663_ = v___y_1819_;
v___y_1664_ = v_argsArray_1818_;
v___y_1665_ = v___y_1813_;
v___y_1666_ = v___y_1820_;
v___y_1667_ = v___y_1824_;
v___y_1668_ = v___y_1823_;
v___y_1669_ = v___x_1840_;
goto v___jp_1646_;
}
}
}
}
v___jp_1841_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1849_, v___y_1845_, v___y_1843_, v___y_1854_, v___y_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = l_Lean_LibrarySuggestions_select(v_a_1861_, v___y_1859_, v___y_1845_, v___y_1843_, v___y_1854_, v___y_1857_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; size_t v_sz_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v_sz_1864_ = lean_array_size(v_a_1863_);
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1863_, v_sz_1864_, v___x_1865_, v___y_1846_, v___y_1855_, v___y_1849_, v___y_1856_, v___y_1851_, v___y_1845_, v___y_1843_, v___y_1854_, v___y_1857_);
lean_dec(v_a_1863_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___y_1810_ = v___y_1842_;
v___y_1811_ = v___y_1853_;
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___y_1858_;
v___y_1814_ = v___y_1848_;
v___y_1815_ = v___y_1847_;
v___y_1816_ = v___y_1850_;
v___y_1817_ = v___y_1852_;
v_argsArray_1818_ = v_a_1867_;
v___y_1819_ = v___y_1855_;
v___y_1820_ = v___y_1849_;
v___y_1821_ = v___y_1856_;
v___y_1822_ = v___y_1851_;
v___y_1823_ = v___y_1845_;
v___y_1824_ = v___y_1843_;
v___y_1825_ = v___y_1854_;
v___y_1826_ = v___y_1857_;
goto v___jp_1809_;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v___y_1858_);
lean_dec(v___y_1853_);
lean_dec(v___y_1850_);
lean_dec(v___y_1847_);
lean_dec(v___y_1844_);
lean_dec(v___y_1842_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v_a_1868_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1866_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v___y_1858_);
lean_dec(v___y_1853_);
lean_dec(v___y_1850_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1844_);
lean_dec(v___y_1842_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v_a_1876_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1862_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1862_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1853_);
lean_dec(v___y_1850_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1844_);
lean_dec(v___y_1842_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v_a_1884_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1860_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1860_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
v___jp_1892_:
{
lean_object* v_config_1911_; uint8_t v_suggestions_1912_; 
v_config_1911_ = lean_ctor_get(v___y_1907_, 0);
lean_inc_ref(v_config_1911_);
lean_dec_ref(v___y_1907_);
v_suggestions_1912_ = lean_ctor_get_uint8(v_config_1911_, sizeof(void*)*3 + 26);
if (v_suggestions_1912_ == 0)
{
lean_dec_ref(v_config_1911_);
lean_dec_ref(v___f_1195_);
v___y_1810_ = v___y_1893_;
v___y_1811_ = v___y_1903_;
v___y_1812_ = v___y_1895_;
v___y_1813_ = v___y_1909_;
v___y_1814_ = v___y_1898_;
v___y_1815_ = v___y_1897_;
v___y_1816_ = v___y_1900_;
v___y_1817_ = v___y_1902_;
v_argsArray_1818_ = v___y_1910_;
v___y_1819_ = v___y_1905_;
v___y_1820_ = v___y_1899_;
v___y_1821_ = v___y_1906_;
v___y_1822_ = v___y_1901_;
v___y_1823_ = v___y_1896_;
v___y_1824_ = v___y_1894_;
v___y_1825_ = v___y_1904_;
v___y_1826_ = v___y_1908_;
goto v___jp_1809_;
}
else
{
lean_object* v_maxSuggestions_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_maxSuggestions_1913_ = lean_ctor_get(v_config_1911_, 2);
lean_inc(v_maxSuggestions_1913_);
lean_dec_ref(v_config_1911_);
v___x_1914_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1915_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1913_) == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(100u);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1914_);
lean_ctor_set(v___x_1917_, 2, v___f_1195_);
lean_ctor_set(v___x_1917_, 3, v___x_1915_);
v___y_1842_ = v___y_1893_;
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1896_;
v___y_1846_ = v___y_1910_;
v___y_1847_ = v___y_1897_;
v___y_1848_ = v___y_1898_;
v___y_1849_ = v___y_1899_;
v___y_1850_ = v___y_1900_;
v___y_1851_ = v___y_1901_;
v___y_1852_ = v___y_1902_;
v___y_1853_ = v___y_1903_;
v___y_1854_ = v___y_1904_;
v___y_1855_ = v___y_1905_;
v___y_1856_ = v___y_1906_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___x_1917_;
goto v___jp_1841_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1919_; 
v_val_1918_ = lean_ctor_get(v_maxSuggestions_1913_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v_maxSuggestions_1913_, 1);
v___x_1919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1919_, 0, v_val_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1914_);
lean_ctor_set(v___x_1919_, 2, v___f_1195_);
lean_ctor_set(v___x_1919_, 3, v___x_1915_);
v___y_1842_ = v___y_1893_;
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1896_;
v___y_1846_ = v___y_1910_;
v___y_1847_ = v___y_1897_;
v___y_1848_ = v___y_1898_;
v___y_1849_ = v___y_1899_;
v___y_1850_ = v___y_1900_;
v___y_1851_ = v___y_1901_;
v___y_1852_ = v___y_1902_;
v___y_1853_ = v___y_1903_;
v___y_1854_ = v___y_1904_;
v___y_1855_ = v___y_1905_;
v___y_1856_ = v___y_1906_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___x_1919_;
goto v___jp_1841_;
}
}
}
v___jp_1920_:
{
uint8_t v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = 0;
lean_inc(v___y_1929_);
v___x_1937_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1929_, v___x_1936_, v___y_1933_, v___y_1932_, v___y_1925_);
if (lean_obj_tag(v___x_1937_) == 0)
{
if (lean_obj_tag(v___y_1926_) == 1)
{
lean_object* v_a_1938_; lean_object* v_val_1939_; lean_object* v___x_1940_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_val_1939_ = lean_ctor_get(v___y_1926_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v___y_1926_, 1);
v___x_1940_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1939_);
lean_dec(v_val_1939_);
lean_inc(v___y_1934_);
v___y_1893_ = v___y_1934_;
v___y_1894_ = v___y_1927_;
v___y_1895_ = v___y_1930_;
v___y_1896_ = v___y_1924_;
v___y_1897_ = v___y_1935_;
v___y_1898_ = v___x_1936_;
v___y_1899_ = v___y_1921_;
v___y_1900_ = v___y_1934_;
v___y_1901_ = v___y_1922_;
v___y_1902_ = v___y_1923_;
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v_a_1938_;
v___y_1908_ = v___y_1925_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___x_1940_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1942_; 
lean_dec(v___y_1926_);
v_a_1941_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1942_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1934_);
v___y_1893_ = v___y_1934_;
v___y_1894_ = v___y_1927_;
v___y_1895_ = v___y_1930_;
v___y_1896_ = v___y_1924_;
v___y_1897_ = v___y_1935_;
v___y_1898_ = v___x_1936_;
v___y_1899_ = v___y_1921_;
v___y_1900_ = v___y_1934_;
v___y_1901_ = v___y_1922_;
v___y_1902_ = v___y_1923_;
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v_a_1941_;
v___y_1908_ = v___y_1925_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___x_1942_;
goto v___jp_1892_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1926_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v_a_1943_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1937_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1937_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
v___jp_1951_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Syntax_getOptional_x3f(v___y_1955_);
lean_dec(v___y_1955_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_box(0);
v___y_1921_ = v___y_1957_;
v___y_1922_ = v___y_1958_;
v___y_1923_ = v___y_1959_;
v___y_1924_ = v___y_1954_;
v___y_1925_ = v___y_1964_;
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1965_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1952_;
v___y_1931_ = v___y_1963_;
v___y_1932_ = v___y_1961_;
v___y_1933_ = v___y_1962_;
v___y_1934_ = v___y_1966_;
v___y_1935_ = v___x_1968_;
goto v___jp_1920_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_val_1969_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1967_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_val_1969_);
lean_dec(v___x_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_val_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
v___y_1921_ = v___y_1957_;
v___y_1922_ = v___y_1958_;
v___y_1923_ = v___y_1959_;
v___y_1924_ = v___y_1954_;
v___y_1925_ = v___y_1964_;
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1965_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1952_;
v___y_1931_ = v___y_1963_;
v___y_1932_ = v___y_1961_;
v___y_1933_ = v___y_1962_;
v___y_1934_ = v___y_1966_;
v___y_1935_ = v___x_1974_;
goto v___jp_1920_;
}
}
}
}
v___jp_1977_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_unsigned_to_nat(4u);
v___x_1994_ = l_Lean_Syntax_getArg(v___y_1980_, v___x_1993_);
lean_dec(v___y_1980_);
v___x_1995_ = l_Lean_Syntax_getOptional_x3f(v___x_1994_);
lean_dec(v___x_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_box(0);
v___y_1952_ = v___y_1979_;
v___y_1953_ = v___y_1990_;
v___y_1954_ = v___y_1989_;
v___y_1955_ = v___y_1982_;
v___y_1956_ = v_args_1984_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1983_;
v___y_1960_ = v___y_1978_;
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1985_;
v___y_1963_ = v___y_1987_;
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_1981_;
v___y_1966_ = v___x_1996_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_val_1997_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1995_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_val_1997_);
lean_dec(v___x_1995_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_val_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
v___y_1952_ = v___y_1979_;
v___y_1953_ = v___y_1990_;
v___y_1954_ = v___y_1989_;
v___y_1955_ = v___y_1982_;
v___y_1956_ = v_args_1984_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1983_;
v___y_1960_ = v___y_1978_;
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1985_;
v___y_1963_ = v___y_1987_;
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_1981_;
v___y_1966_ = v___x_2002_;
goto v___jp_1951_;
}
}
}
}
v___jp_2006_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2021_ = lean_unsigned_to_nat(3u);
v___x_2022_ = l_Lean_Syntax_getArg(v___y_2008_, v___x_2021_);
v___x_2023_ = l_Lean_Syntax_isNone(v___x_2022_);
if (v___x_2023_ == 0)
{
uint8_t v___x_2024_; 
lean_inc(v___x_2022_);
v___x_2024_ = l_Lean_Syntax_matchesNull(v___x_2022_, v___x_2005_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec(v___x_2022_);
lean_dec(v_o_2012_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2025_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2026_ = l_Lean_Syntax_getArg(v___x_2022_, v___x_1206_);
lean_dec(v___x_2022_);
v___x_2027_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
lean_inc_ref(v___x_1192_);
v___x_2028_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_2027_);
lean_inc(v___x_2026_);
v___x_2029_ = l_Lean_Syntax_isOfKind(v___x_2026_, v___x_2028_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec(v___x_2026_);
lean_dec(v_o_2012_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2030_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; lean_object* v_args_2032_; lean_object* v___x_2033_; 
v___x_2031_ = l_Lean_Syntax_getArg(v___x_2026_, v___x_2005_);
lean_dec(v___x_2026_);
v_args_2032_ = l_Lean_Syntax_getArgs(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_args_2032_);
v___y_1978_ = v___y_2007_;
v___y_1979_ = v_o_2012_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2011_;
v_args_1984_ = v___x_2033_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
goto v___jp_1977_;
}
}
}
else
{
lean_object* v___x_2034_; 
lean_dec(v___x_2022_);
v___x_2034_ = lean_box(0);
v___y_1978_ = v___y_2007_;
v___y_1979_ = v_o_2012_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2011_;
v_args_1984_ = v___x_2034_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
goto v___jp_1977_;
}
}
v___jp_2035_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2045_ = lean_unsigned_to_nat(2u);
v___x_2046_ = l_Lean_Syntax_getArg(v_stx_1190_, v___x_2045_);
v___x_2047_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
lean_inc_ref(v___x_1192_);
v___x_2048_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_2047_);
lean_inc(v___x_2046_);
v___x_2049_ = l_Lean_Syntax_isOfKind(v___x_2046_, v___x_2048_);
lean_dec(v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v___x_2046_);
lean_dec(v_bang_2036_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2050_;
}
else
{
lean_object* v_cfg_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v_cfg_2051_ = l_Lean_Syntax_getArg(v___x_2046_, v___x_1206_);
v___x_2052_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
lean_inc_ref(v___x_1192_);
v___x_2053_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_2052_);
lean_inc(v_cfg_2051_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v_cfg_2051_, v___x_2053_);
lean_dec(v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v_cfg_2051_);
lean_dec(v___x_2046_);
lean_dec(v_bang_2036_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = l_Lean_Syntax_getArg(v___x_2046_, v___x_2005_);
v___x_2057_ = l_Lean_Syntax_getArg(v___x_2046_, v___x_2045_);
v___x_2058_ = l_Lean_Syntax_isNone(v___x_2057_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
lean_inc(v___x_2057_);
v___x_2059_ = l_Lean_Syntax_matchesNull(v___x_2057_, v___x_2005_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec(v___x_2057_);
lean_dec(v___x_2056_);
lean_dec(v_cfg_2051_);
lean_dec(v___x_2046_);
lean_dec(v_bang_2036_);
lean_dec(v_tk_1207_);
lean_dec_ref(v___f_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_2060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2060_;
}
else
{
lean_object* v_o_2061_; lean_object* v___x_2062_; 
v_o_2061_ = l_Lean_Syntax_getArg(v___x_2057_, v___x_1206_);
lean_dec(v___x_2057_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_o_2061_);
v___y_2007_ = v_cfg_2051_;
v___y_2008_ = v___x_2046_;
v___y_2009_ = v_bang_2036_;
v___y_2010_ = v___x_2056_;
v___y_2011_ = v___x_2049_;
v_o_2012_ = v___x_2062_;
v___y_2013_ = v___y_2037_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
goto v___jp_2006_;
}
}
else
{
lean_object* v___x_2063_; 
lean_dec(v___x_2057_);
v___x_2063_ = lean_box(0);
v___y_2007_ = v_cfg_2051_;
v___y_2008_ = v___x_2046_;
v___y_2009_ = v_bang_2036_;
v___y_2010_ = v___x_2056_;
v___y_2011_ = v___x_2049_;
v_o_2012_ = v___x_2063_;
v___y_2013_ = v___y_2037_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
goto v___jp_2006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2071_, lean_object* v_stx_2072_, lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v___x_2076_, lean_object* v___f_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_35264__boxed_2087_; uint8_t v___x_35265__boxed_2088_; lean_object* v_res_2089_; 
v___x_35264__boxed_2087_ = lean_unbox(v___x_2071_);
v___x_35265__boxed_2088_ = lean_unbox(v___x_2073_);
v_res_2089_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35264__boxed_2087_, v_stx_2072_, v___x_35265__boxed_2088_, v___x_2074_, v___x_2075_, v___x_2076_, v___f_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v_stx_2072_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2099_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_stx_2099_, v___x_2112_);
v___x_2114_ = 1;
v___f_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2116_ = lean_box(v___x_2113_);
v___x_2117_ = lean_box(v___x_2114_);
v___y_2118_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2118_, 0, v___x_2116_);
lean_closure_set(v___y_2118_, 1, v_stx_2099_);
lean_closure_set(v___y_2118_, 2, v___x_2117_);
lean_closure_set(v___y_2118_, 3, v___x_2109_);
lean_closure_set(v___y_2118_, 4, v___x_2110_);
lean_closure_set(v___y_2118_, 5, v___x_2111_);
lean_closure_set(v___y_2118_, 6, v___f_2115_);
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2119_, 0, v___y_2118_);
v___x_2120_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2119_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2132_, lean_object* v_as_2133_, lean_object* v_as_x27_2134_, lean_object* v_b_2135_, lean_object* v_a_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2132_, v_as_x27_2134_, v_b_2135_, v___y_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2147_, lean_object* v_as_2148_, lean_object* v_as_x27_2149_, lean_object* v_b_2150_, lean_object* v_a_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2147_, v_as_2148_, v_as_x27_2149_, v_b_2150_, v_a_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_as_x27_2149_);
lean_dec(v_as_2148_);
lean_dec(v___x_2147_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2162_, lean_object* v_ref_2163_, lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2163_, v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_ref_2176_, lean_object* v_msg_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2175_, v_ref_2176_, v_msg_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_ref_2176_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2188_, lean_object* v_ref_2189_, lean_object* v_constName_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2189_, v_constName_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_ref_2202_, lean_object* v_constName_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2201_, v_ref_2202_, v_constName_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v_ref_2202_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2214_, lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2215_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_msg_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2226_, v_msg_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2238_, v___y_2245_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_opt_2249_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2260_, lean_object* v_ref_2261_, lean_object* v_msg_2262_, lean_object* v_declHint_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2261_, v_msg_2262_, v_declHint_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_ref_2275_, lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2274_, v_ref_2275_, v_msg_2276_, v_declHint_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v_ref_2275_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2288_, lean_object* v_declHint_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2288_, v_declHint_2289_, v___y_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2300_, v_declHint_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2312_, lean_object* v_msgData_2313_, uint8_t v_severity_2314_, uint8_t v_isSilent_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2312_, v_msgData_2313_, v_severity_2314_, v_isSilent_2315_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2326_, lean_object* v_msgData_2327_, lean_object* v_severity_2328_, lean_object* v_isSilent_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v_severity_boxed_2339_; uint8_t v_isSilent_boxed_2340_; lean_object* v_res_2341_; 
v_severity_boxed_2339_ = lean_unbox(v_severity_2328_);
v_isSilent_boxed_2340_ = lean_unbox(v_isSilent_2329_);
v_res_2341_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2326_, v_msgData_2327_, v_severity_boxed_2339_, v_isSilent_boxed_2340_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_ref_2326_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2349_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2350_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2352_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2353_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2349_, v___x_2350_, v___x_2351_, v___x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2384_ = l_Lean_addBuiltinDeclarationRanges(v___x_2382_, v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2387_, lean_object* v_as_x27_2388_, lean_object* v_b_2389_, lean_object* v___y_2390_){
_start:
{
if (lean_obj_tag(v_as_x27_2388_) == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_b_2389_);
return v___x_2392_;
}
else
{
lean_object* v_head_2393_; lean_object* v_tail_2394_; lean_object* v_ref_2395_; uint8_t v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_head_2393_ = lean_ctor_get(v_as_x27_2388_, 0);
v_tail_2394_ = lean_ctor_get(v_as_x27_2388_, 1);
v_ref_2395_ = lean_ctor_get(v___y_2390_, 2);
v___x_2396_ = 1;
v___x_2397_ = 0;
v___x_2398_ = l_Lean_SourceInfo_fromRef(v_ref_2395_, v___x_2397_);
v___x_2399_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2400_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2401_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2398_);
v___x_2402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2398_);
lean_ctor_set(v___x_2402_, 1, v___x_2400_);
lean_ctor_set(v___x_2402_, 2, v___x_2401_);
lean_inc(v_head_2393_);
v___x_2403_ = l_Lean_mkCIdentFrom(v___x_2387_, v_head_2393_, v___x_2396_);
lean_inc_ref(v___x_2402_);
v___x_2404_ = l_Lean_Syntax_node3(v___x_2398_, v___x_2399_, v___x_2402_, v___x_2402_, v___x_2403_);
v___x_2405_ = lean_array_push(v_b_2389_, v___x_2404_);
v_as_x27_2388_ = v_tail_2394_;
v_b_2389_ = v___x_2405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2407_, lean_object* v_as_x27_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2407_, v_as_x27_2408_, v_b_2409_, v___y_2410_);
lean_dec_ref(v___y_2410_);
lean_dec(v_as_x27_2408_);
lean_dec(v___x_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2413_, size_t v_sz_2414_, size_t v_i_2415_, lean_object* v_b_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_lt(v_i_2415_, v_sz_2414_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_b_2416_);
return v___x_2427_;
}
else
{
lean_object* v_a_2428_; lean_object* v_name_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_a_2428_ = lean_array_uget_borrowed(v_as_2413_, v_i_2415_);
v_name_2429_ = lean_ctor_get(v_a_2428_, 0);
lean_inc(v_name_2429_);
v___x_2430_ = l_Lean_mkIdent(v_name_2429_);
lean_inc(v___x_2430_);
v___x_2431_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2430_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2433_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2433_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2430_, v_a_2432_, v_b_2416_, v___y_2423_);
lean_dec(v_a_2432_);
lean_dec(v___x_2430_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; size_t v___x_2435_; size_t v___x_2436_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2435_ = ((size_t)1ULL);
v___x_2436_ = lean_usize_add(v_i_2415_, v___x_2435_);
v_i_2415_ = v___x_2436_;
v_b_2416_ = v_a_2434_;
goto _start;
}
else
{
return v___x_2433_;
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v___x_2430_);
lean_dec_ref(v_b_2416_);
v_a_2438_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2431_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2431_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2446_, lean_object* v_sz_2447_, lean_object* v_i_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
size_t v_sz_boxed_2459_; size_t v_i_boxed_2460_; lean_object* v_res_2461_; 
v_sz_boxed_2459_ = lean_unbox_usize(v_sz_2447_);
lean_dec(v_sz_2447_);
v_i_boxed_2460_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2446_, v_sz_boxed_2459_, v_i_boxed_2460_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v_as_2446_);
return v_res_2461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2464_);
return v___x_2466_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_unsigned_to_nat(32u);
v___x_2468_ = lean_mk_empty_array_with_capacity(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2470_ = ((size_t)5ULL);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_unsigned_to_nat(32u);
v___x_2473_ = lean_mk_empty_array_with_capacity(v___x_2472_);
v___x_2474_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2475_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v___x_2473_);
lean_ctor_set(v___x_2475_, 2, v___x_2471_);
lean_ctor_set(v___x_2475_, 3, v___x_2471_);
lean_ctor_set_usize(v___x_2475_, 4, v___x_2470_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
lean_ctor_set(v___x_2478_, 3, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2480_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___x_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2490_, lean_object* v_stx_2491_, uint8_t v___x_2492_, lean_object* v___x_2493_, lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v___f_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
if (v___x_2490_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_2506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v_tk_2508_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; uint8_t v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; uint8_t v___y_2626_; lean_object* v_stxForSuggestion_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; uint8_t v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2689_; uint8_t v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; uint8_t v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; uint8_t v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; uint8_t v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; uint8_t v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; uint8_t v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; uint8_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; uint8_t v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; uint8_t v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; uint8_t v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; uint8_t v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; lean_object* v_stxForExecution_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; uint8_t v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; uint8_t v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3080_; uint8_t v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; uint8_t v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3137_; uint8_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; uint8_t v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; uint8_t v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v_argsArray_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; uint8_t v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v_args_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___x_3438_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v_o_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v_bang_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v_tk_2508_ = l_Lean_Syntax_getArg(v_stx_2491_, v___x_2507_);
v___x_3438_ = lean_unsigned_to_nat(1u);
v___x_3497_ = l_Lean_Syntax_getArg(v_stx_2491_, v___x_3438_);
v___x_3498_ = l_Lean_Syntax_isNone(v___x_3497_);
if (v___x_3498_ == 0)
{
uint8_t v___x_3499_; 
lean_inc(v___x_3497_);
v___x_3499_ = l_Lean_Syntax_matchesNull(v___x_3497_, v___x_3438_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___x_3497_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3500_;
}
else
{
lean_object* v_bang_3501_; lean_object* v___x_3502_; 
v_bang_3501_ = l_Lean_Syntax_getArg(v___x_3497_, v___x_2507_);
lean_dec(v___x_3497_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_bang_3501_);
v_bang_3469_ = v___x_3502_;
v___y_3470_ = v___y_2497_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
v___y_3476_ = v___y_2503_;
v___y_3477_ = v___y_2504_;
goto v___jp_3468_;
}
}
else
{
lean_object* v___x_3503_; 
lean_dec(v___x_3497_);
v___x_3503_ = lean_box(0);
v_bang_3469_ = v___x_3503_;
v___y_3470_ = v___y_2497_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
v___y_3476_ = v___y_2503_;
v___y_3477_ = v___y_2504_;
goto v___jp_3468_;
}
v___jp_2509_:
{
lean_object* v_usedTheorems_2516_; lean_object* v_diag_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2559_; 
v_usedTheorems_2516_ = lean_ctor_get(v___y_2511_, 0);
v_diag_2517_ = lean_ctor_get(v___y_2511_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___y_2511_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2519_ = v___y_2511_;
v_isShared_2520_ = v_isSharedCheck_2559_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_diag_2517_);
lean_inc(v_usedTheorems_2516_);
lean_dec(v___y_2511_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2559_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2510_, v_usedTheorems_2516_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec_ref(v_usedTheorems_2516_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v_ref_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v_ref_2523_ = lean_ctor_get(v___y_2514_, 2);
v___x_2524_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 1, v_a_2522_);
lean_ctor_set(v___x_2519_, 0, v___x_2524_);
v___x_2526_ = v___x_2519_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_a_2522_);
v___x_2526_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_ctor_set(v___x_2528_, 2, v___x_2527_);
lean_ctor_set(v___x_2528_, 3, v___x_2527_);
lean_ctor_set(v___x_2528_, 4, v___x_2527_);
lean_ctor_set(v___x_2528_, 5, v___x_2527_);
lean_inc(v_ref_2523_);
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_ref_2523_);
v___x_2530_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2531_ = 4;
v___x_2532_ = l_Lean_MessageData_nil;
v___x_2533_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2508_, v___x_2528_, v___x_2529_, v___x_2530_, v___x_2527_, v___x_2531_, v___x_2532_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2533_, 0);
lean_dec(v_unused_2541_);
v___x_2535_ = v___x_2533_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v___x_2533_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v_diag_2517_);
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_diag_2517_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v_diag_2517_);
v_a_2542_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2533_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2533_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_del_object(v___x_2519_);
lean_dec_ref(v_diag_2517_);
lean_dec(v_tk_2508_);
v_a_2551_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2521_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2521_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
v___jp_2560_:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2564_, v___y_2563_, v___y_2562_, v___y_2567_, v___y_2561_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2572_ = l_Lean_Meta_simpAll(v_a_2570_, v___y_2568_, v___y_2566_, v___x_2571_, v___y_2563_, v___y_2562_, v___y_2567_, v___y_2561_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v_fst_2574_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v_fst_2574_ = lean_ctor_get(v_a_2573_, 0);
if (lean_obj_tag(v_fst_2574_) == 0)
{
lean_object* v_snd_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_snd_2575_ = lean_ctor_get(v_a_2573_, 1);
lean_inc(v_snd_2575_);
lean_dec(v_a_2573_);
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2576_, v___y_2564_, v___y_2563_, v___y_2562_, v___y_2567_, v___y_2561_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_dec_ref_known(v___x_2577_, 1);
v___y_2510_ = v___y_2565_;
v___y_2511_ = v_snd_2575_;
v___y_2512_ = v___y_2563_;
v___y_2513_ = v___y_2562_;
v___y_2514_ = v___y_2567_;
v___y_2515_ = v___y_2561_;
goto v___jp_2509_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_snd_2575_);
lean_dec(v___y_2565_);
lean_dec(v_tk_2508_);
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2604_; 
lean_inc_ref(v_fst_2574_);
v_snd_2586_ = lean_ctor_get(v_a_2573_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_a_2573_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v_a_2573_, 0);
lean_dec(v_unused_2605_);
v___x_2588_ = v_a_2573_;
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_dec(v_a_2573_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_val_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v_val_2590_ = lean_ctor_get(v_fst_2574_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_fst_2574_, 1);
v___x_2591_ = lean_box(0);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 1);
lean_ctor_set(v___x_2588_, 1, v___x_2591_);
lean_ctor_set(v___x_2588_, 0, v_val_2590_);
v___x_2593_ = v___x_2588_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_val_2590_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2593_, v___y_2564_, v___y_2563_, v___y_2562_, v___y_2567_, v___y_2561_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_dec_ref_known(v___x_2594_, 1);
v___y_2510_ = v___y_2565_;
v___y_2511_ = v_snd_2586_;
v___y_2512_ = v___y_2563_;
v___y_2513_ = v___y_2562_;
v___y_2514_ = v___y_2567_;
v___y_2515_ = v___y_2561_;
goto v___jp_2509_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_snd_2586_);
lean_dec(v___y_2565_);
lean_dec(v_tk_2508_);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v___y_2565_);
lean_dec(v_tk_2508_);
v_a_2606_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2572_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2572_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec(v_tk_2508_);
v_a_2614_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2569_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2569_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
v___jp_2622_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2637_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2624_, v___x_2492_, v___y_2623_, v___x_2492_, v___x_2636_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2624_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
if (lean_obj_tag(v___y_2625_) == 0)
{
lean_object* v_ctx_2639_; lean_object* v_simprocs_2640_; 
v_ctx_2639_ = lean_ctor_get(v_a_2638_, 0);
lean_inc_ref(v_ctx_2639_);
v_simprocs_2640_ = lean_ctor_get(v_a_2638_, 1);
lean_inc_ref(v_simprocs_2640_);
lean_dec(v_a_2638_);
v___y_2561_ = v___y_2635_;
v___y_2562_ = v___y_2633_;
v___y_2563_ = v___y_2632_;
v___y_2564_ = v___y_2629_;
v___y_2565_ = v_stxForSuggestion_2627_;
v___y_2566_ = v_simprocs_2640_;
v___y_2567_ = v___y_2634_;
v___y_2568_ = v_ctx_2639_;
goto v___jp_2560_;
}
else
{
lean_dec_ref_known(v___y_2625_, 1);
if (v___y_2626_ == 0)
{
lean_object* v_ctx_2641_; lean_object* v_simprocs_2642_; 
v_ctx_2641_ = lean_ctor_get(v_a_2638_, 0);
lean_inc_ref(v_ctx_2641_);
v_simprocs_2642_ = lean_ctor_get(v_a_2638_, 1);
lean_inc_ref(v_simprocs_2642_);
lean_dec(v_a_2638_);
v___y_2561_ = v___y_2635_;
v___y_2562_ = v___y_2633_;
v___y_2563_ = v___y_2632_;
v___y_2564_ = v___y_2629_;
v___y_2565_ = v_stxForSuggestion_2627_;
v___y_2566_ = v_simprocs_2642_;
v___y_2567_ = v___y_2634_;
v___y_2568_ = v_ctx_2641_;
goto v___jp_2560_;
}
else
{
lean_object* v_ctx_2643_; lean_object* v_simprocs_2644_; lean_object* v___x_2645_; 
v_ctx_2643_ = lean_ctor_get(v_a_2638_, 0);
lean_inc_ref(v_ctx_2643_);
v_simprocs_2644_ = lean_ctor_get(v_a_2638_, 1);
lean_inc_ref(v_simprocs_2644_);
lean_dec(v_a_2638_);
v___x_2645_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2643_);
v___y_2561_ = v___y_2635_;
v___y_2562_ = v___y_2633_;
v___y_2563_ = v___y_2632_;
v___y_2564_ = v___y_2629_;
v___y_2565_ = v_stxForSuggestion_2627_;
v___y_2566_ = v_simprocs_2644_;
v___y_2567_ = v___y_2634_;
v___y_2568_ = v___x_2645_;
goto v___jp_2560_;
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_stxForSuggestion_2627_);
lean_dec(v___y_2625_);
lean_dec(v_tk_2508_);
v_a_2646_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2637_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2637_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2654_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_inc_ref_n(v___y_2656_, 2);
v___x_2676_ = l_Array_append___redArg(v___y_2656_, v___y_2675_);
lean_dec_ref(v___y_2675_);
lean_inc_n(v___y_2672_, 3);
lean_inc_n(v___y_2673_, 5);
v___x_2677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2673_);
lean_ctor_set(v___x_2677_, 1, v___y_2672_);
lean_ctor_set(v___x_2677_, 2, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___y_2673_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2681_ = l_Lean_Syntax_SepArray_ofElems(v___x_2680_, v___y_2659_);
lean_dec_ref(v___y_2659_);
v___x_2682_ = l_Array_append___redArg(v___y_2656_, v___x_2681_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2673_);
lean_ctor_set(v___x_2683_, 1, v___y_2672_);
lean_ctor_set(v___x_2683_, 2, v___x_2682_);
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___y_2673_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_Syntax_node3(v___y_2673_, v___y_2672_, v___x_2679_, v___x_2683_, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node5(v___y_2673_, v___y_2658_, v___y_2670_, v___y_2668_, v___y_2664_, v___x_2677_, v___x_2686_);
v___y_2623_ = v___y_2655_;
v___y_2624_ = v___y_2665_;
v___y_2625_ = v___y_2669_;
v___y_2626_ = v___y_2663_;
v_stxForSuggestion_2627_ = v___x_2687_;
v___y_2628_ = v___y_2674_;
v___y_2629_ = v___y_2666_;
v___y_2630_ = v___y_2661_;
v___y_2631_ = v___y_2671_;
v___y_2632_ = v___y_2662_;
v___y_2633_ = v___y_2667_;
v___y_2634_ = v___y_2660_;
v___y_2635_ = v___y_2657_;
goto v___jp_2622_;
}
v___jp_2688_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_inc_ref(v___y_2689_);
v___x_2710_ = l_Array_append___redArg(v___y_2689_, v___y_2709_);
lean_dec_ref(v___y_2709_);
lean_inc(v___y_2705_);
lean_inc(v___y_2706_);
v___x_2711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2711_, 0, v___y_2706_);
lean_ctor_set(v___x_2711_, 1, v___y_2705_);
lean_ctor_set(v___x_2711_, 2, v___x_2710_);
if (lean_obj_tag(v___y_2708_) == 1)
{
lean_object* v_val_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_val_2712_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___y_2708_, 1);
v___x_2713_ = l_Lean_SourceInfo_fromRef(v_val_2712_, v___x_2492_);
lean_dec(v_val_2712_);
v___x_2714_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Array_mkArray1___redArg(v___x_2715_);
v___y_2655_ = v___y_2690_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2693_;
v___y_2660_ = v___y_2694_;
v___y_2661_ = v___y_2695_;
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___x_2711_;
v___y_2665_ = v___y_2698_;
v___y_2666_ = v___y_2699_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2700_;
v___y_2669_ = v___y_2704_;
v___y_2670_ = v___y_2703_;
v___y_2671_ = v___y_2702_;
v___y_2672_ = v___y_2705_;
v___y_2673_ = v___y_2706_;
v___y_2674_ = v___y_2707_;
v___y_2675_ = v___x_2716_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2717_; 
lean_dec(v___y_2708_);
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2655_ = v___y_2690_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2693_;
v___y_2660_ = v___y_2694_;
v___y_2661_ = v___y_2695_;
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___x_2711_;
v___y_2665_ = v___y_2698_;
v___y_2666_ = v___y_2699_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2700_;
v___y_2669_ = v___y_2704_;
v___y_2670_ = v___y_2703_;
v___y_2671_ = v___y_2702_;
v___y_2672_ = v___y_2705_;
v___y_2673_ = v___y_2706_;
v___y_2674_ = v___y_2707_;
v___y_2675_ = v___x_2717_;
goto v___jp_2654_;
}
}
v___jp_2718_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_inc_ref_n(v___y_2723_, 2);
v___x_2740_ = l_Array_append___redArg(v___y_2723_, v___y_2739_);
lean_dec_ref(v___y_2739_);
lean_inc_n(v___y_2729_, 3);
lean_inc_n(v___y_2728_, 5);
v___x_2741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2728_);
lean_ctor_set(v___x_2741_, 1, v___y_2729_);
lean_ctor_set(v___x_2741_, 2, v___x_2740_);
v___x_2742_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___y_2728_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2745_ = l_Lean_Syntax_SepArray_ofElems(v___x_2744_, v___y_2721_);
lean_dec_ref(v___y_2721_);
v___x_2746_ = l_Array_append___redArg(v___y_2723_, v___x_2745_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2747_, 0, v___y_2728_);
lean_ctor_set(v___x_2747_, 1, v___y_2729_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
v___x_2748_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___y_2728_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Lean_Syntax_node3(v___y_2728_, v___y_2729_, v___x_2743_, v___x_2747_, v___x_2749_);
v___x_2751_ = l_Lean_Syntax_node5(v___y_2728_, v___y_2726_, v___y_2731_, v___y_2735_, v___y_2733_, v___x_2741_, v___x_2750_);
v___y_2623_ = v___y_2719_;
v___y_2624_ = v___y_2730_;
v___y_2625_ = v___y_2736_;
v___y_2626_ = v___y_2727_;
v_stxForSuggestion_2627_ = v___x_2751_;
v___y_2628_ = v___y_2738_;
v___y_2629_ = v___y_2732_;
v___y_2630_ = v___y_2724_;
v___y_2631_ = v___y_2737_;
v___y_2632_ = v___y_2725_;
v___y_2633_ = v___y_2734_;
v___y_2634_ = v___y_2722_;
v___y_2635_ = v___y_2720_;
goto v___jp_2622_;
}
v___jp_2752_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_inc_ref(v___y_2756_);
v___x_2774_ = l_Array_append___redArg(v___y_2756_, v___y_2773_);
lean_dec_ref(v___y_2773_);
lean_inc(v___y_2763_);
lean_inc(v___y_2762_);
v___x_2775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2775_, 0, v___y_2762_);
lean_ctor_set(v___x_2775_, 1, v___y_2763_);
lean_ctor_set(v___x_2775_, 2, v___x_2774_);
if (lean_obj_tag(v___y_2772_) == 1)
{
lean_object* v_val_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_val_2776_ = lean_ctor_get(v___y_2772_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v___y_2772_, 1);
v___x_2777_ = l_Lean_SourceInfo_fromRef(v_val_2776_, v___x_2492_);
lean_dec(v_val_2776_);
v___x_2778_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Array_mkArray1___redArg(v___x_2779_);
v___y_2719_ = v___y_2753_;
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2757_;
v___y_2723_ = v___y_2756_;
v___y_2724_ = v___y_2758_;
v___y_2725_ = v___y_2759_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2766_;
v___y_2732_ = v___y_2765_;
v___y_2733_ = v___x_2775_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2767_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2769_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___x_2780_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2781_; 
lean_dec(v___y_2772_);
v___x_2781_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2719_ = v___y_2753_;
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2757_;
v___y_2723_ = v___y_2756_;
v___y_2724_ = v___y_2758_;
v___y_2725_ = v___y_2759_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2766_;
v___y_2732_ = v___y_2765_;
v___y_2733_ = v___x_2775_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2767_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2769_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___x_2781_;
goto v___jp_2718_;
}
}
v___jp_2782_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_inc_ref_n(v___y_2800_, 2);
v___x_2803_ = l_Array_append___redArg(v___y_2800_, v___y_2802_);
lean_dec_ref(v___y_2802_);
lean_inc_n(v___y_2797_, 2);
lean_inc_n(v___y_2801_, 2);
v___x_2804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___y_2801_);
lean_ctor_set(v___x_2804_, 1, v___y_2797_);
lean_ctor_set(v___x_2804_, 2, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2805_, 0, v___y_2801_);
lean_ctor_set(v___x_2805_, 1, v___y_2797_);
lean_ctor_set(v___x_2805_, 2, v___y_2800_);
v___x_2806_ = l_Lean_Syntax_node5(v___y_2801_, v___y_2791_, v___y_2786_, v___y_2793_, v___y_2798_, v___x_2804_, v___x_2805_);
v___y_2623_ = v___y_2783_;
v___y_2624_ = v___y_2790_;
v___y_2625_ = v___y_2795_;
v___y_2626_ = v___y_2789_;
v_stxForSuggestion_2627_ = v___x_2806_;
v___y_2628_ = v___y_2799_;
v___y_2629_ = v___y_2792_;
v___y_2630_ = v___y_2787_;
v___y_2631_ = v___y_2796_;
v___y_2632_ = v___y_2788_;
v___y_2633_ = v___y_2794_;
v___y_2634_ = v___y_2785_;
v___y_2635_ = v___y_2784_;
goto v___jp_2622_;
}
v___jp_2807_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc_ref(v___y_2824_);
v___x_2828_ = l_Array_append___redArg(v___y_2824_, v___y_2827_);
lean_dec_ref(v___y_2827_);
lean_inc(v___y_2822_);
lean_inc(v___y_2826_);
v___x_2829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2829_, 0, v___y_2826_);
lean_ctor_set(v___x_2829_, 1, v___y_2822_);
lean_ctor_set(v___x_2829_, 2, v___x_2828_);
if (lean_obj_tag(v___y_2825_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_val_2830_ = lean_ctor_get(v___y_2825_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___y_2825_, 1);
v___x_2831_ = l_Lean_SourceInfo_fromRef(v_val_2830_, v___x_2492_);
lean_dec(v_val_2830_);
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Array_mkArray1___redArg(v___x_2833_);
v___y_2783_ = v___y_2808_;
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2811_;
v___y_2787_ = v___y_2812_;
v___y_2788_ = v___y_2813_;
v___y_2789_ = v___y_2814_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2819_;
v___y_2794_ = v___y_2818_;
v___y_2795_ = v___y_2821_;
v___y_2796_ = v___y_2820_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2829_;
v___y_2799_ = v___y_2823_;
v___y_2800_ = v___y_2824_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___x_2834_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2835_; 
lean_dec(v___y_2825_);
v___x_2835_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2783_ = v___y_2808_;
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2811_;
v___y_2787_ = v___y_2812_;
v___y_2788_ = v___y_2813_;
v___y_2789_ = v___y_2814_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2819_;
v___y_2794_ = v___y_2818_;
v___y_2795_ = v___y_2821_;
v___y_2796_ = v___y_2820_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2829_;
v___y_2799_ = v___y_2823_;
v___y_2800_ = v___y_2824_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___x_2835_;
goto v___jp_2782_;
}
}
v___jp_2836_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc_ref_n(v___y_2851_, 2);
v___x_2857_ = l_Array_append___redArg(v___y_2851_, v___y_2856_);
lean_dec_ref(v___y_2856_);
lean_inc_n(v___y_2841_, 2);
lean_inc_n(v___y_2848_, 2);
v___x_2858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___y_2848_);
lean_ctor_set(v___x_2858_, 1, v___y_2841_);
lean_ctor_set(v___x_2858_, 2, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___y_2848_);
lean_ctor_set(v___x_2859_, 1, v___y_2841_);
lean_ctor_set(v___x_2859_, 2, v___y_2851_);
v___x_2860_ = l_Lean_Syntax_node5(v___y_2848_, v___y_2839_, v___y_2854_, v___y_2849_, v___y_2845_, v___x_2858_, v___x_2859_);
v___y_2623_ = v___y_2837_;
v___y_2624_ = v___y_2846_;
v___y_2625_ = v___y_2852_;
v___y_2626_ = v___y_2844_;
v_stxForSuggestion_2627_ = v___x_2860_;
v___y_2628_ = v___y_2855_;
v___y_2629_ = v___y_2847_;
v___y_2630_ = v___y_2842_;
v___y_2631_ = v___y_2853_;
v___y_2632_ = v___y_2843_;
v___y_2633_ = v___y_2850_;
v___y_2634_ = v___y_2840_;
v___y_2635_ = v___y_2838_;
goto v___jp_2622_;
}
v___jp_2861_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_inc_ref(v___y_2875_);
v___x_2882_ = l_Array_append___redArg(v___y_2875_, v___y_2881_);
lean_dec_ref(v___y_2881_);
lean_inc(v___y_2866_);
lean_inc(v___y_2874_);
v___x_2883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2874_);
lean_ctor_set(v___x_2883_, 1, v___y_2866_);
lean_ctor_set(v___x_2883_, 2, v___x_2882_);
if (lean_obj_tag(v___y_2880_) == 1)
{
lean_object* v_val_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_val_2884_ = lean_ctor_get(v___y_2880_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v___y_2880_, 1);
v___x_2885_ = l_Lean_SourceInfo_fromRef(v_val_2884_, v___x_2492_);
lean_dec(v_val_2884_);
v___x_2886_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = l_Array_mkArray1___redArg(v___x_2887_);
v___y_2837_ = v___y_2862_;
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2864_;
v___y_2840_ = v___y_2865_;
v___y_2841_ = v___y_2866_;
v___y_2842_ = v___y_2867_;
v___y_2843_ = v___y_2868_;
v___y_2844_ = v___y_2869_;
v___y_2845_ = v___x_2883_;
v___y_2846_ = v___y_2870_;
v___y_2847_ = v___y_2871_;
v___y_2848_ = v___y_2874_;
v___y_2849_ = v___y_2873_;
v___y_2850_ = v___y_2872_;
v___y_2851_ = v___y_2875_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2876_;
v___y_2854_ = v___y_2878_;
v___y_2855_ = v___y_2879_;
v___y_2856_ = v___x_2888_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2889_; 
lean_dec(v___y_2880_);
v___x_2889_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2837_ = v___y_2862_;
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2864_;
v___y_2840_ = v___y_2865_;
v___y_2841_ = v___y_2866_;
v___y_2842_ = v___y_2867_;
v___y_2843_ = v___y_2868_;
v___y_2844_ = v___y_2869_;
v___y_2845_ = v___x_2883_;
v___y_2846_ = v___y_2870_;
v___y_2847_ = v___y_2871_;
v___y_2848_ = v___y_2874_;
v___y_2849_ = v___y_2873_;
v___y_2850_ = v___y_2872_;
v___y_2851_ = v___y_2875_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2876_;
v___y_2854_ = v___y_2878_;
v___y_2855_ = v___y_2879_;
v___y_2856_ = v___x_2889_;
goto v___jp_2836_;
}
}
v___jp_2890_:
{
lean_object* v_ref_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_ref_2908_ = lean_ctor_get(v___y_2894_, 2);
v___x_2909_ = l_Lean_SourceInfo_fromRef(v_ref_2908_, v___y_2907_);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2911_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2910_);
v___x_2912_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2916_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2902_) == 1)
{
lean_object* v_val_2917_; lean_object* v___x_2918_; 
v_val_2917_ = lean_ctor_get(v___y_2902_, 0);
lean_inc(v_val_2917_);
lean_dec_ref_known(v___y_2902_, 1);
v___x_2918_ = l_Array_mkArray1___redArg(v_val_2917_);
v___y_2689_ = v___x_2916_;
v___y_2690_ = v___y_2891_;
v___y_2691_ = v___y_2892_;
v___y_2692_ = v___x_2911_;
v___y_2693_ = v___y_2893_;
v___y_2694_ = v___y_2894_;
v___y_2695_ = v___y_2895_;
v___y_2696_ = v___y_2896_;
v___y_2697_ = v___y_2897_;
v___y_2698_ = v___y_2898_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2904_;
v___y_2703_ = v___x_2914_;
v___y_2704_ = v___y_2903_;
v___y_2705_ = v___x_2915_;
v___y_2706_ = v___x_2909_;
v___y_2707_ = v___y_2905_;
v___y_2708_ = v___y_2906_;
v___y_2709_ = v___x_2918_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2919_; 
lean_dec(v___y_2902_);
v___x_2919_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2689_ = v___x_2916_;
v___y_2690_ = v___y_2891_;
v___y_2691_ = v___y_2892_;
v___y_2692_ = v___x_2911_;
v___y_2693_ = v___y_2893_;
v___y_2694_ = v___y_2894_;
v___y_2695_ = v___y_2895_;
v___y_2696_ = v___y_2896_;
v___y_2697_ = v___y_2897_;
v___y_2698_ = v___y_2898_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2904_;
v___y_2703_ = v___x_2914_;
v___y_2704_ = v___y_2903_;
v___y_2705_ = v___x_2915_;
v___y_2706_ = v___x_2909_;
v___y_2707_ = v___y_2905_;
v___y_2708_ = v___y_2906_;
v___y_2709_ = v___x_2919_;
goto v___jp_2688_;
}
}
v___jp_2920_:
{
lean_object* v___x_2937_; lean_object* v_a_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2937_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2923_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = lean_array_get_size(v___y_2922_);
v___x_2940_ = lean_nat_dec_eq(v___x_2939_, v___x_2507_);
if (v___x_2940_ == 0)
{
if (lean_obj_tag(v___y_2925_) == 0)
{
v___y_2891_ = v___y_2921_;
v___y_2892_ = v___y_2936_;
v___y_2893_ = v___y_2922_;
v___y_2894_ = v___y_2935_;
v___y_2895_ = v___y_2931_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2926_;
v___y_2898_ = v_stxForExecution_2928_;
v___y_2899_ = v___y_2930_;
v___y_2900_ = v_a_2938_;
v___y_2901_ = v___y_2934_;
v___y_2902_ = v___y_2924_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2932_;
v___y_2905_ = v___y_2929_;
v___y_2906_ = v___y_2927_;
v___y_2907_ = v___x_2940_;
goto v___jp_2890_;
}
else
{
if (v___y_2926_ == 0)
{
v___y_2891_ = v___y_2921_;
v___y_2892_ = v___y_2936_;
v___y_2893_ = v___y_2922_;
v___y_2894_ = v___y_2935_;
v___y_2895_ = v___y_2931_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2926_;
v___y_2898_ = v_stxForExecution_2928_;
v___y_2899_ = v___y_2930_;
v___y_2900_ = v_a_2938_;
v___y_2901_ = v___y_2934_;
v___y_2902_ = v___y_2924_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2932_;
v___y_2905_ = v___y_2929_;
v___y_2906_ = v___y_2927_;
v___y_2907_ = v___y_2926_;
goto v___jp_2890_;
}
else
{
lean_object* v_ref_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_ref_2941_ = lean_ctor_get(v___y_2935_, 2);
v___x_2942_ = l_Lean_SourceInfo_fromRef(v_ref_2941_, v___x_2940_);
v___x_2943_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2944_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2943_);
v___x_2945_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_2946_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2949_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2924_) == 1)
{
lean_object* v_val_2950_; lean_object* v___x_2951_; 
v_val_2950_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_val_2950_);
lean_dec_ref_known(v___y_2924_, 1);
v___x_2951_ = l_Array_mkArray1___redArg(v_val_2950_);
v___y_2753_ = v___y_2921_;
v___y_2754_ = v___y_2936_;
v___y_2755_ = v___y_2922_;
v___y_2756_ = v___x_2949_;
v___y_2757_ = v___y_2935_;
v___y_2758_ = v___y_2931_;
v___y_2759_ = v___y_2933_;
v___y_2760_ = v___x_2944_;
v___y_2761_ = v___y_2926_;
v___y_2762_ = v___x_2942_;
v___y_2763_ = v___x_2948_;
v___y_2764_ = v_stxForExecution_2928_;
v___y_2765_ = v___y_2930_;
v___y_2766_ = v___x_2947_;
v___y_2767_ = v_a_2938_;
v___y_2768_ = v___y_2934_;
v___y_2769_ = v___y_2932_;
v___y_2770_ = v___y_2925_;
v___y_2771_ = v___y_2929_;
v___y_2772_ = v___y_2927_;
v___y_2773_ = v___x_2951_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2952_; 
lean_dec(v___y_2924_);
v___x_2952_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2753_ = v___y_2921_;
v___y_2754_ = v___y_2936_;
v___y_2755_ = v___y_2922_;
v___y_2756_ = v___x_2949_;
v___y_2757_ = v___y_2935_;
v___y_2758_ = v___y_2931_;
v___y_2759_ = v___y_2933_;
v___y_2760_ = v___x_2944_;
v___y_2761_ = v___y_2926_;
v___y_2762_ = v___x_2942_;
v___y_2763_ = v___x_2948_;
v___y_2764_ = v_stxForExecution_2928_;
v___y_2765_ = v___y_2930_;
v___y_2766_ = v___x_2947_;
v___y_2767_ = v_a_2938_;
v___y_2768_ = v___y_2934_;
v___y_2769_ = v___y_2932_;
v___y_2770_ = v___y_2925_;
v___y_2771_ = v___y_2929_;
v___y_2772_ = v___y_2927_;
v___y_2773_ = v___x_2952_;
goto v___jp_2752_;
}
}
}
}
else
{
lean_dec_ref(v___y_2922_);
if (lean_obj_tag(v___y_2925_) == 0)
{
lean_object* v_ref_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_ref_2953_ = lean_ctor_get(v___y_2935_, 2);
v___x_2954_ = 0;
v___x_2955_ = l_Lean_SourceInfo_fromRef(v_ref_2953_, v___x_2954_);
v___x_2956_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2957_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2956_);
v___x_2958_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2962_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2924_) == 1)
{
lean_object* v_val_2963_; lean_object* v___x_2964_; 
v_val_2963_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_val_2963_);
lean_dec_ref_known(v___y_2924_, 1);
v___x_2964_ = l_Array_mkArray1___redArg(v_val_2963_);
v___y_2808_ = v___y_2921_;
v___y_2809_ = v___y_2936_;
v___y_2810_ = v___y_2935_;
v___y_2811_ = v___x_2960_;
v___y_2812_ = v___y_2931_;
v___y_2813_ = v___y_2933_;
v___y_2814_ = v___y_2926_;
v___y_2815_ = v_stxForExecution_2928_;
v___y_2816_ = v___x_2957_;
v___y_2817_ = v___y_2930_;
v___y_2818_ = v___y_2934_;
v___y_2819_ = v_a_2938_;
v___y_2820_ = v___y_2932_;
v___y_2821_ = v___y_2925_;
v___y_2822_ = v___x_2961_;
v___y_2823_ = v___y_2929_;
v___y_2824_ = v___x_2962_;
v___y_2825_ = v___y_2927_;
v___y_2826_ = v___x_2955_;
v___y_2827_ = v___x_2964_;
goto v___jp_2807_;
}
else
{
lean_object* v___x_2965_; 
lean_dec(v___y_2924_);
v___x_2965_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2808_ = v___y_2921_;
v___y_2809_ = v___y_2936_;
v___y_2810_ = v___y_2935_;
v___y_2811_ = v___x_2960_;
v___y_2812_ = v___y_2931_;
v___y_2813_ = v___y_2933_;
v___y_2814_ = v___y_2926_;
v___y_2815_ = v_stxForExecution_2928_;
v___y_2816_ = v___x_2957_;
v___y_2817_ = v___y_2930_;
v___y_2818_ = v___y_2934_;
v___y_2819_ = v_a_2938_;
v___y_2820_ = v___y_2932_;
v___y_2821_ = v___y_2925_;
v___y_2822_ = v___x_2961_;
v___y_2823_ = v___y_2929_;
v___y_2824_ = v___x_2962_;
v___y_2825_ = v___y_2927_;
v___y_2826_ = v___x_2955_;
v___y_2827_ = v___x_2965_;
goto v___jp_2807_;
}
}
else
{
lean_object* v_ref_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_ref_2966_ = lean_ctor_get(v___y_2935_, 2);
v___x_2967_ = 0;
v___x_2968_ = l_Lean_SourceInfo_fromRef(v_ref_2966_, v___x_2967_);
v___x_2969_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2970_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2969_);
v___x_2971_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2975_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2924_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2977_; 
v_val_2976_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___y_2924_, 1);
v___x_2977_ = l_Array_mkArray1___redArg(v_val_2976_);
v___y_2862_ = v___y_2921_;
v___y_2863_ = v___y_2936_;
v___y_2864_ = v___x_2970_;
v___y_2865_ = v___y_2935_;
v___y_2866_ = v___x_2974_;
v___y_2867_ = v___y_2931_;
v___y_2868_ = v___y_2933_;
v___y_2869_ = v___y_2926_;
v___y_2870_ = v_stxForExecution_2928_;
v___y_2871_ = v___y_2930_;
v___y_2872_ = v___y_2934_;
v___y_2873_ = v_a_2938_;
v___y_2874_ = v___x_2968_;
v___y_2875_ = v___x_2975_;
v___y_2876_ = v___y_2932_;
v___y_2877_ = v___y_2925_;
v___y_2878_ = v___x_2973_;
v___y_2879_ = v___y_2929_;
v___y_2880_ = v___y_2927_;
v___y_2881_ = v___x_2977_;
goto v___jp_2861_;
}
else
{
lean_object* v___x_2978_; 
lean_dec(v___y_2924_);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2862_ = v___y_2921_;
v___y_2863_ = v___y_2936_;
v___y_2864_ = v___x_2970_;
v___y_2865_ = v___y_2935_;
v___y_2866_ = v___x_2974_;
v___y_2867_ = v___y_2931_;
v___y_2868_ = v___y_2933_;
v___y_2869_ = v___y_2926_;
v___y_2870_ = v_stxForExecution_2928_;
v___y_2871_ = v___y_2930_;
v___y_2872_ = v___y_2934_;
v___y_2873_ = v_a_2938_;
v___y_2874_ = v___x_2968_;
v___y_2875_ = v___x_2975_;
v___y_2876_ = v___y_2932_;
v___y_2877_ = v___y_2925_;
v___y_2878_ = v___x_2973_;
v___y_2879_ = v___y_2929_;
v___y_2880_ = v___y_2927_;
v___y_2881_ = v___x_2978_;
goto v___jp_2861_;
}
}
}
}
v___jp_2979_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_inc_ref_n(v___y_2984_, 2);
v___x_3002_ = l_Array_append___redArg(v___y_2984_, v___y_3001_);
lean_dec_ref(v___y_3001_);
lean_inc_n(v___y_2987_, 3);
lean_inc_n(v___y_2988_, 5);
v___x_3003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3003_, 0, v___y_2988_);
lean_ctor_set(v___x_3003_, 1, v___y_2987_);
lean_ctor_set(v___x_3003_, 2, v___x_3002_);
v___x_3004_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___y_2988_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3007_ = l_Lean_Syntax_SepArray_ofElems(v___x_3006_, v___y_2982_);
v___x_3008_ = l_Array_append___redArg(v___y_2984_, v___x_3007_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___y_2988_);
lean_ctor_set(v___x_3009_, 1, v___y_2987_);
lean_ctor_set(v___x_3009_, 2, v___x_3008_);
v___x_3010_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___y_2988_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_Syntax_node3(v___y_2988_, v___y_2987_, v___x_3005_, v___x_3009_, v___x_3011_);
lean_inc(v___y_2985_);
v___x_3013_ = l_Lean_Syntax_node5(v___y_2988_, v___y_2990_, v___y_2996_, v___y_2985_, v___y_2997_, v___x_3003_, v___x_3012_);
v___y_2921_ = v___y_2980_;
v___y_2922_ = v___y_2982_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v___y_2992_;
v___y_2925_ = v___y_2991_;
v___y_2926_ = v___y_2986_;
v___y_2927_ = v___y_2999_;
v_stxForExecution_2928_ = v___x_3013_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_2998_;
v___y_2931_ = v___y_2989_;
v___y_2932_ = v___y_2983_;
v___y_2933_ = v___y_2993_;
v___y_2934_ = v___y_2981_;
v___y_2935_ = v___y_2994_;
v___y_2936_ = v___y_2995_;
goto v___jp_2920_;
}
v___jp_3014_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_inc_ref(v___y_3019_);
v___x_3036_ = l_Array_append___redArg(v___y_3019_, v___y_3035_);
lean_dec_ref(v___y_3035_);
lean_inc(v___y_3022_);
lean_inc(v___y_3023_);
v___x_3037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3037_, 0, v___y_3023_);
lean_ctor_set(v___x_3037_, 1, v___y_3022_);
lean_ctor_set(v___x_3037_, 2, v___x_3036_);
if (lean_obj_tag(v___y_3034_) == 1)
{
lean_object* v_val_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_val_3038_ = lean_ctor_get(v___y_3034_, 0);
v___x_3039_ = l_Lean_SourceInfo_fromRef(v_val_3038_, v___x_2492_);
v___x_3040_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Array_mkArray1___redArg(v___x_3041_);
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3019_;
v___y_2985_ = v___y_3020_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___x_3037_;
v___y_2998_ = v___y_3030_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3033_;
v___y_3001_ = v___x_3042_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3019_;
v___y_2985_ = v___y_3020_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___x_3037_;
v___y_2998_ = v___y_3030_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3033_;
v___y_3001_ = v___x_3043_;
goto v___jp_2979_;
}
}
v___jp_3044_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_inc_ref_n(v___y_3052_, 2);
v___x_3067_ = l_Array_append___redArg(v___y_3052_, v___y_3066_);
lean_dec_ref(v___y_3066_);
lean_inc_n(v___y_3054_, 3);
lean_inc_n(v___y_3046_, 5);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3046_);
lean_ctor_set(v___x_3068_, 1, v___y_3054_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___y_3046_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3072_ = l_Lean_Syntax_SepArray_ofElems(v___x_3071_, v___y_3048_);
v___x_3073_ = l_Array_append___redArg(v___y_3052_, v___x_3072_);
lean_dec_ref(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3074_, 0, v___y_3046_);
lean_ctor_set(v___x_3074_, 1, v___y_3054_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
v___x_3075_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___y_3046_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Lean_Syntax_node3(v___y_3046_, v___y_3054_, v___x_3070_, v___x_3074_, v___x_3076_);
lean_inc(v___y_3050_);
v___x_3078_ = l_Lean_Syntax_node5(v___y_3046_, v___y_3051_, v___y_3063_, v___y_3050_, v___y_3055_, v___x_3068_, v___x_3077_);
v___y_2921_ = v___y_3045_;
v___y_2922_ = v___y_3048_;
v___y_2923_ = v___y_3050_;
v___y_2924_ = v___y_3058_;
v___y_2925_ = v___y_3057_;
v___y_2926_ = v___y_3053_;
v___y_2927_ = v___y_3064_;
v_stxForExecution_2928_ = v___x_3078_;
v___y_2929_ = v___y_3065_;
v___y_2930_ = v___y_3062_;
v___y_2931_ = v___y_3056_;
v___y_2932_ = v___y_3049_;
v___y_2933_ = v___y_3059_;
v___y_2934_ = v___y_3047_;
v___y_2935_ = v___y_3060_;
v___y_2936_ = v___y_3061_;
goto v___jp_2920_;
}
v___jp_3079_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_inc_ref(v___y_3087_);
v___x_3101_ = l_Array_append___redArg(v___y_3087_, v___y_3100_);
lean_dec_ref(v___y_3100_);
lean_inc(v___y_3089_);
lean_inc(v___y_3080_);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3080_);
lean_ctor_set(v___x_3102_, 1, v___y_3089_);
lean_ctor_set(v___x_3102_, 2, v___x_3101_);
if (lean_obj_tag(v___y_3099_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_val_3103_ = lean_ctor_get(v___y_3099_, 0);
v___x_3104_ = l_Lean_SourceInfo_fromRef(v_val_3103_, v___x_2492_);
v___x_3105_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Array_mkArray1___redArg(v___x_3106_);
v___y_3045_ = v___y_3081_;
v___y_3046_ = v___y_3080_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3089_;
v___y_3055_ = v___x_3102_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3096_;
v___y_3062_ = v___y_3095_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3099_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___x_3107_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3108_; 
v___x_3108_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3045_ = v___y_3081_;
v___y_3046_ = v___y_3080_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3089_;
v___y_3055_ = v___x_3102_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3096_;
v___y_3062_ = v___y_3095_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3099_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___x_3108_;
goto v___jp_3044_;
}
}
v___jp_3109_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_inc_ref_n(v___y_3111_, 2);
v___x_3132_ = l_Array_append___redArg(v___y_3111_, v___y_3131_);
lean_dec_ref(v___y_3131_);
lean_inc_n(v___y_3117_, 2);
lean_inc_n(v___y_3121_, 2);
v___x_3133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3133_, 0, v___y_3121_);
lean_ctor_set(v___x_3133_, 1, v___y_3117_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___y_3121_);
lean_ctor_set(v___x_3134_, 1, v___y_3117_);
lean_ctor_set(v___x_3134_, 2, v___y_3111_);
lean_inc(v___y_3115_);
v___x_3135_ = l_Lean_Syntax_node5(v___y_3121_, v___y_3124_, v___y_3116_, v___y_3115_, v___y_3120_, v___x_3133_, v___x_3134_);
v___y_2921_ = v___y_3110_;
v___y_2922_ = v___y_3112_;
v___y_2923_ = v___y_3115_;
v___y_2924_ = v___y_3123_;
v___y_2925_ = v___y_3122_;
v___y_2926_ = v___y_3118_;
v___y_2927_ = v___y_3129_;
v_stxForExecution_2928_ = v___x_3135_;
v___y_2929_ = v___y_3130_;
v___y_2930_ = v___y_3128_;
v___y_2931_ = v___y_3119_;
v___y_2932_ = v___y_3114_;
v___y_2933_ = v___y_3125_;
v___y_2934_ = v___y_3113_;
v___y_2935_ = v___y_3126_;
v___y_2936_ = v___y_3127_;
goto v___jp_2920_;
}
v___jp_3136_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_inc_ref(v___y_3137_);
v___x_3158_ = l_Array_append___redArg(v___y_3137_, v___y_3157_);
lean_dec_ref(v___y_3157_);
lean_inc(v___y_3144_);
lean_inc(v___y_3147_);
v___x_3159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___y_3147_);
lean_ctor_set(v___x_3159_, 1, v___y_3144_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
if (lean_obj_tag(v___y_3156_) == 1)
{
lean_object* v_val_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_val_3160_ = lean_ctor_get(v___y_3156_, 0);
v___x_3161_ = l_Lean_SourceInfo_fromRef(v_val_3160_, v___x_2492_);
v___x_3162_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Array_mkArray1___redArg(v___x_3163_);
v___y_3110_ = v___y_3138_;
v___y_3111_ = v___y_3137_;
v___y_3112_ = v___y_3139_;
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3141_;
v___y_3115_ = v___y_3142_;
v___y_3116_ = v___y_3143_;
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___x_3159_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3150_;
v___y_3125_ = v___y_3151_;
v___y_3126_ = v___y_3152_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3153_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3155_;
v___y_3131_ = v___x_3164_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3165_; 
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3110_ = v___y_3138_;
v___y_3111_ = v___y_3137_;
v___y_3112_ = v___y_3139_;
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3141_;
v___y_3115_ = v___y_3142_;
v___y_3116_ = v___y_3143_;
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___x_3159_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3150_;
v___y_3125_ = v___y_3151_;
v___y_3126_ = v___y_3152_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3153_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3155_;
v___y_3131_ = v___x_3165_;
goto v___jp_3109_;
}
}
v___jp_3166_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_inc_ref_n(v___y_3183_, 2);
v___x_3189_ = l_Array_append___redArg(v___y_3183_, v___y_3188_);
lean_dec_ref(v___y_3188_);
lean_inc_n(v___y_3172_, 2);
lean_inc_n(v___y_3170_, 2);
v___x_3190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3190_, 0, v___y_3170_);
lean_ctor_set(v___x_3190_, 1, v___y_3172_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3170_);
lean_ctor_set(v___x_3191_, 1, v___y_3172_);
lean_ctor_set(v___x_3191_, 2, v___y_3183_);
lean_inc(v___y_3174_);
v___x_3192_ = l_Lean_Syntax_node5(v___y_3170_, v___y_3179_, v___y_3168_, v___y_3174_, v___y_3182_, v___x_3190_, v___x_3191_);
v___y_2921_ = v___y_3167_;
v___y_2922_ = v___y_3169_;
v___y_2923_ = v___y_3174_;
v___y_2924_ = v___y_3178_;
v___y_2925_ = v___y_3177_;
v___y_2926_ = v___y_3175_;
v___y_2927_ = v___y_3186_;
v_stxForExecution_2928_ = v___x_3192_;
v___y_2929_ = v___y_3187_;
v___y_2930_ = v___y_3185_;
v___y_2931_ = v___y_3176_;
v___y_2932_ = v___y_3173_;
v___y_2933_ = v___y_3180_;
v___y_2934_ = v___y_3171_;
v___y_2935_ = v___y_3181_;
v___y_2936_ = v___y_3184_;
goto v___jp_2920_;
}
v___jp_3193_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc_ref(v___y_3209_);
v___x_3215_ = l_Array_append___redArg(v___y_3209_, v___y_3214_);
lean_dec_ref(v___y_3214_);
lean_inc(v___y_3199_);
lean_inc(v___y_3196_);
v___x_3216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___y_3196_);
lean_ctor_set(v___x_3216_, 1, v___y_3199_);
lean_ctor_set(v___x_3216_, 2, v___x_3215_);
if (lean_obj_tag(v___y_3213_) == 1)
{
lean_object* v_val_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_val_3217_ = lean_ctor_get(v___y_3213_, 0);
v___x_3218_ = l_Lean_SourceInfo_fromRef(v_val_3217_, v___x_2492_);
v___x_3219_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l_Array_mkArray1___redArg(v___x_3220_);
v___y_3167_ = v___y_3194_;
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3197_;
v___y_3170_ = v___y_3196_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___y_3202_;
v___y_3176_ = v___y_3203_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___x_3216_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3212_;
v___y_3188_ = v___x_3221_;
goto v___jp_3166_;
}
else
{
lean_object* v___x_3222_; 
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3167_ = v___y_3194_;
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3197_;
v___y_3170_ = v___y_3196_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___y_3202_;
v___y_3176_ = v___y_3203_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___x_3216_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3212_;
v___y_3188_ = v___x_3222_;
goto v___jp_3166_;
}
}
v___jp_3223_:
{
lean_object* v_ref_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_ref_3240_ = lean_ctor_get(v___y_3234_, 2);
v___x_3241_ = l_Lean_SourceInfo_fromRef(v_ref_3240_, v___y_3239_);
v___x_3242_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3243_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3242_);
v___x_3244_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_3245_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3248_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3232_) == 1)
{
lean_object* v_val_3249_; lean_object* v___x_3250_; 
v_val_3249_ = lean_ctor_get(v___y_3232_, 0);
lean_inc(v_val_3249_);
v___x_3250_ = l_Array_mkArray1___redArg(v_val_3249_);
v___y_3015_ = v___y_3224_;
v___y_3016_ = v___y_3225_;
v___y_3017_ = v___y_3226_;
v___y_3018_ = v___y_3227_;
v___y_3019_ = v___x_3248_;
v___y_3020_ = v___y_3228_;
v___y_3021_ = v___y_3229_;
v___y_3022_ = v___x_3247_;
v___y_3023_ = v___x_3241_;
v___y_3024_ = v___y_3230_;
v___y_3025_ = v___x_3243_;
v___y_3026_ = v___y_3231_;
v___y_3027_ = v___y_3232_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___y_3236_;
v___y_3031_ = v___x_3246_;
v___y_3032_ = v___y_3235_;
v___y_3033_ = v___y_3238_;
v___y_3034_ = v___y_3237_;
v___y_3035_ = v___x_3250_;
goto v___jp_3014_;
}
else
{
lean_object* v___x_3251_; 
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3015_ = v___y_3224_;
v___y_3016_ = v___y_3225_;
v___y_3017_ = v___y_3226_;
v___y_3018_ = v___y_3227_;
v___y_3019_ = v___x_3248_;
v___y_3020_ = v___y_3228_;
v___y_3021_ = v___y_3229_;
v___y_3022_ = v___x_3247_;
v___y_3023_ = v___x_3241_;
v___y_3024_ = v___y_3230_;
v___y_3025_ = v___x_3243_;
v___y_3026_ = v___y_3231_;
v___y_3027_ = v___y_3232_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___y_3236_;
v___y_3031_ = v___x_3246_;
v___y_3032_ = v___y_3235_;
v___y_3033_ = v___y_3238_;
v___y_3034_ = v___y_3237_;
v___y_3035_ = v___x_3251_;
goto v___jp_3014_;
}
}
v___jp_3252_:
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = lean_array_get_size(v_argsArray_3259_);
v___x_3269_ = lean_nat_dec_eq(v___x_3268_, v___x_2507_);
if (v___x_3269_ == 0)
{
if (lean_obj_tag(v___y_3255_) == 0)
{
v___y_3224_ = v___y_3253_;
v___y_3225_ = v___y_3265_;
v___y_3226_ = v_argsArray_3259_;
v___y_3227_ = v___y_3263_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___y_3257_;
v___y_3230_ = v___y_3262_;
v___y_3231_ = v___y_3255_;
v___y_3232_ = v___y_3256_;
v___y_3233_ = v___y_3264_;
v___y_3234_ = v___y_3266_;
v___y_3235_ = v___y_3267_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v___y_3258_;
v___y_3238_ = v___y_3260_;
v___y_3239_ = v___x_3269_;
goto v___jp_3223_;
}
else
{
if (v___y_3257_ == 0)
{
v___y_3224_ = v___y_3253_;
v___y_3225_ = v___y_3265_;
v___y_3226_ = v_argsArray_3259_;
v___y_3227_ = v___y_3263_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___y_3257_;
v___y_3230_ = v___y_3262_;
v___y_3231_ = v___y_3255_;
v___y_3232_ = v___y_3256_;
v___y_3233_ = v___y_3264_;
v___y_3234_ = v___y_3266_;
v___y_3235_ = v___y_3267_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v___y_3258_;
v___y_3238_ = v___y_3260_;
v___y_3239_ = v___y_3257_;
goto v___jp_3223_;
}
else
{
lean_object* v_ref_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_ref_3270_ = lean_ctor_get(v___y_3266_, 2);
v___x_3271_ = l_Lean_SourceInfo_fromRef(v_ref_3270_, v___x_3269_);
v___x_3272_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3273_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3272_);
v___x_3274_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_3275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3278_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3256_) == 1)
{
lean_object* v_val_3279_; lean_object* v___x_3280_; 
v_val_3279_ = lean_ctor_get(v___y_3256_, 0);
lean_inc(v_val_3279_);
v___x_3280_ = l_Array_mkArray1___redArg(v_val_3279_);
v___y_3080_ = v___x_3271_;
v___y_3081_ = v___y_3253_;
v___y_3082_ = v___y_3265_;
v___y_3083_ = v_argsArray_3259_;
v___y_3084_ = v___y_3263_;
v___y_3085_ = v___y_3254_;
v___y_3086_ = v___x_3273_;
v___y_3087_ = v___x_3278_;
v___y_3088_ = v___y_3257_;
v___y_3089_ = v___x_3277_;
v___y_3090_ = v___y_3262_;
v___y_3091_ = v___y_3255_;
v___y_3092_ = v___y_3256_;
v___y_3093_ = v___y_3264_;
v___y_3094_ = v___y_3266_;
v___y_3095_ = v___y_3261_;
v___y_3096_ = v___y_3267_;
v___y_3097_ = v___x_3276_;
v___y_3098_ = v___y_3260_;
v___y_3099_ = v___y_3258_;
v___y_3100_ = v___x_3280_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3080_ = v___x_3271_;
v___y_3081_ = v___y_3253_;
v___y_3082_ = v___y_3265_;
v___y_3083_ = v_argsArray_3259_;
v___y_3084_ = v___y_3263_;
v___y_3085_ = v___y_3254_;
v___y_3086_ = v___x_3273_;
v___y_3087_ = v___x_3278_;
v___y_3088_ = v___y_3257_;
v___y_3089_ = v___x_3277_;
v___y_3090_ = v___y_3262_;
v___y_3091_ = v___y_3255_;
v___y_3092_ = v___y_3256_;
v___y_3093_ = v___y_3264_;
v___y_3094_ = v___y_3266_;
v___y_3095_ = v___y_3261_;
v___y_3096_ = v___y_3267_;
v___y_3097_ = v___x_3276_;
v___y_3098_ = v___y_3260_;
v___y_3099_ = v___y_3258_;
v___y_3100_ = v___x_3281_;
goto v___jp_3079_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3255_) == 0)
{
lean_object* v_ref_3282_; uint8_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_ref_3282_ = lean_ctor_get(v___y_3266_, 2);
v___x_3283_ = 0;
v___x_3284_ = l_Lean_SourceInfo_fromRef(v_ref_3282_, v___x_3283_);
v___x_3285_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3286_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3285_);
v___x_3287_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3291_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3256_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3293_; 
v_val_3292_ = lean_ctor_get(v___y_3256_, 0);
lean_inc(v_val_3292_);
v___x_3293_ = l_Array_mkArray1___redArg(v_val_3292_);
v___y_3137_ = v___x_3291_;
v___y_3138_ = v___y_3253_;
v___y_3139_ = v_argsArray_3259_;
v___y_3140_ = v___y_3265_;
v___y_3141_ = v___y_3263_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___x_3290_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3262_;
v___y_3147_ = v___x_3284_;
v___y_3148_ = v___y_3255_;
v___y_3149_ = v___y_3256_;
v___y_3150_ = v___x_3286_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3266_;
v___y_3153_ = v___y_3261_;
v___y_3154_ = v___y_3267_;
v___y_3155_ = v___y_3260_;
v___y_3156_ = v___y_3258_;
v___y_3157_ = v___x_3293_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3294_; 
v___x_3294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3137_ = v___x_3291_;
v___y_3138_ = v___y_3253_;
v___y_3139_ = v_argsArray_3259_;
v___y_3140_ = v___y_3265_;
v___y_3141_ = v___y_3263_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___x_3290_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3262_;
v___y_3147_ = v___x_3284_;
v___y_3148_ = v___y_3255_;
v___y_3149_ = v___y_3256_;
v___y_3150_ = v___x_3286_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3266_;
v___y_3153_ = v___y_3261_;
v___y_3154_ = v___y_3267_;
v___y_3155_ = v___y_3260_;
v___y_3156_ = v___y_3258_;
v___y_3157_ = v___x_3294_;
goto v___jp_3136_;
}
}
else
{
lean_object* v_ref_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_ref_3295_ = lean_ctor_get(v___y_3266_, 2);
v___x_3296_ = 0;
v___x_3297_ = l_Lean_SourceInfo_fromRef(v_ref_3295_, v___x_3296_);
v___x_3298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3299_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3298_);
v___x_3300_ = l_Lean_SourceInfo_fromRef(v_tk_2508_, v___x_2492_);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3304_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3256_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___y_3256_, 0);
lean_inc(v_val_3305_);
v___x_3306_ = l_Array_mkArray1___redArg(v_val_3305_);
v___y_3194_ = v___y_3253_;
v___y_3195_ = v___x_3302_;
v___y_3196_ = v___x_3297_;
v___y_3197_ = v_argsArray_3259_;
v___y_3198_ = v___y_3265_;
v___y_3199_ = v___x_3303_;
v___y_3200_ = v___y_3263_;
v___y_3201_ = v___y_3254_;
v___y_3202_ = v___y_3257_;
v___y_3203_ = v___y_3262_;
v___y_3204_ = v___y_3255_;
v___y_3205_ = v___y_3256_;
v___y_3206_ = v___x_3299_;
v___y_3207_ = v___y_3264_;
v___y_3208_ = v___y_3266_;
v___y_3209_ = v___x_3304_;
v___y_3210_ = v___y_3261_;
v___y_3211_ = v___y_3267_;
v___y_3212_ = v___y_3260_;
v___y_3213_ = v___y_3258_;
v___y_3214_ = v___x_3306_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3194_ = v___y_3253_;
v___y_3195_ = v___x_3302_;
v___y_3196_ = v___x_3297_;
v___y_3197_ = v_argsArray_3259_;
v___y_3198_ = v___y_3265_;
v___y_3199_ = v___x_3303_;
v___y_3200_ = v___y_3263_;
v___y_3201_ = v___y_3254_;
v___y_3202_ = v___y_3257_;
v___y_3203_ = v___y_3262_;
v___y_3204_ = v___y_3255_;
v___y_3205_ = v___y_3256_;
v___y_3206_ = v___x_3299_;
v___y_3207_ = v___y_3264_;
v___y_3208_ = v___y_3266_;
v___y_3209_ = v___x_3304_;
v___y_3210_ = v___y_3261_;
v___y_3211_ = v___y_3267_;
v___y_3212_ = v___y_3260_;
v___y_3213_ = v___y_3258_;
v___y_3214_ = v___x_3307_;
goto v___jp_3193_;
}
}
}
}
v___jp_3308_:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3316_, v___y_3321_, v___y_3314_, v___y_3315_, v___y_3311_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Lean_LibrarySuggestions_select(v_a_3326_, v___y_3324_, v___y_3321_, v___y_3314_, v___y_3315_, v___y_3311_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; size_t v_sz_3329_; size_t v___x_3330_; lean_object* v___x_3331_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v_sz_3329_ = lean_array_size(v_a_3328_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3328_, v_sz_3329_, v___x_3330_, v___y_3319_, v___y_3323_, v___y_3316_, v___y_3320_, v___y_3310_, v___y_3321_, v___y_3314_, v___y_3315_, v___y_3311_);
lean_dec(v_a_3328_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3331_, 1);
v___y_3253_ = v___y_3309_;
v___y_3254_ = v___y_3312_;
v___y_3255_ = v___y_3318_;
v___y_3256_ = v___y_3317_;
v___y_3257_ = v___y_3313_;
v___y_3258_ = v___y_3322_;
v_argsArray_3259_ = v_a_3332_;
v___y_3260_ = v___y_3323_;
v___y_3261_ = v___y_3316_;
v___y_3262_ = v___y_3320_;
v___y_3263_ = v___y_3310_;
v___y_3264_ = v___y_3321_;
v___y_3265_ = v___y_3314_;
v___y_3266_ = v___y_3315_;
v___y_3267_ = v___y_3311_;
goto v___jp_3252_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3312_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v_a_3333_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3331_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3312_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v_a_3341_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3327_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3327_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3312_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v_a_3349_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3325_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3325_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
v___jp_3357_:
{
lean_object* v_config_3374_; uint8_t v_suggestions_3375_; 
v_config_3374_ = lean_ctor_get(v___y_3359_, 0);
lean_inc_ref(v_config_3374_);
lean_dec_ref(v___y_3359_);
v_suggestions_3375_ = lean_ctor_get_uint8(v_config_3374_, sizeof(void*)*3 + 26);
if (v_suggestions_3375_ == 0)
{
lean_dec_ref(v_config_3374_);
lean_dec_ref(v___f_2496_);
v___y_3253_ = v___y_3358_;
v___y_3254_ = v___y_3362_;
v___y_3255_ = v___y_3368_;
v___y_3256_ = v___y_3367_;
v___y_3257_ = v___y_3363_;
v___y_3258_ = v___y_3372_;
v_argsArray_3259_ = v___y_3373_;
v___y_3260_ = v___y_3371_;
v___y_3261_ = v___y_3366_;
v___y_3262_ = v___y_3369_;
v___y_3263_ = v___y_3360_;
v___y_3264_ = v___y_3370_;
v___y_3265_ = v___y_3364_;
v___y_3266_ = v___y_3365_;
v___y_3267_ = v___y_3361_;
goto v___jp_3252_;
}
else
{
lean_object* v_maxSuggestions_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_maxSuggestions_3376_ = lean_ctor_get(v_config_3374_, 2);
lean_inc(v_maxSuggestions_3376_);
lean_dec_ref(v_config_3374_);
v___x_3377_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3378_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3376_) == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_unsigned_to_nat(100u);
v___x_3380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v___x_3377_);
lean_ctor_set(v___x_3380_, 2, v___f_2496_);
lean_ctor_set(v___x_3380_, 3, v___x_3378_);
v___y_3309_ = v___y_3358_;
v___y_3310_ = v___y_3360_;
v___y_3311_ = v___y_3361_;
v___y_3312_ = v___y_3362_;
v___y_3313_ = v___y_3363_;
v___y_3314_ = v___y_3364_;
v___y_3315_ = v___y_3365_;
v___y_3316_ = v___y_3366_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3368_;
v___y_3319_ = v___y_3373_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3372_;
v___y_3323_ = v___y_3371_;
v___y_3324_ = v___x_3380_;
goto v___jp_3308_;
}
else
{
lean_object* v_val_3381_; lean_object* v___x_3382_; 
v_val_3381_ = lean_ctor_get(v_maxSuggestions_3376_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v_maxSuggestions_3376_, 1);
v___x_3382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3382_, 0, v_val_3381_);
lean_ctor_set(v___x_3382_, 1, v___x_3377_);
lean_ctor_set(v___x_3382_, 2, v___f_2496_);
lean_ctor_set(v___x_3382_, 3, v___x_3378_);
v___y_3309_ = v___y_3358_;
v___y_3310_ = v___y_3360_;
v___y_3311_ = v___y_3361_;
v___y_3312_ = v___y_3362_;
v___y_3313_ = v___y_3363_;
v___y_3314_ = v___y_3364_;
v___y_3315_ = v___y_3365_;
v___y_3316_ = v___y_3366_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3368_;
v___y_3319_ = v___y_3373_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3372_;
v___y_3323_ = v___y_3371_;
v___y_3324_ = v___x_3382_;
goto v___jp_3308_;
}
}
}
v___jp_3383_:
{
uint8_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = 1;
lean_inc(v___y_3386_);
v___x_3399_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3386_, v___x_3398_, v___y_3396_, v___y_3388_, v___y_3385_);
if (lean_obj_tag(v___x_3399_) == 0)
{
if (lean_obj_tag(v___y_3390_) == 1)
{
lean_object* v_a_3400_; lean_object* v_val_3401_; lean_object* v___x_3402_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v_val_3401_ = lean_ctor_get(v___y_3390_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___y_3390_, 1);
v___x_3402_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3401_);
lean_dec(v_val_3401_);
v___y_3358_ = v___x_3398_;
v___y_3359_ = v_a_3400_;
v___y_3360_ = v___y_3384_;
v___y_3361_ = v___y_3385_;
v___y_3362_ = v___y_3386_;
v___y_3363_ = v___y_3387_;
v___y_3364_ = v___y_3389_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___y_3391_;
v___y_3367_ = v___y_3397_;
v___y_3368_ = v___y_3392_;
v___y_3369_ = v___y_3393_;
v___y_3370_ = v___y_3394_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3395_;
v___y_3373_ = v___x_3402_;
goto v___jp_3357_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3404_; 
lean_dec(v___y_3390_);
v_a_3403_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3399_, 1);
v___x_3404_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3358_ = v___x_3398_;
v___y_3359_ = v_a_3403_;
v___y_3360_ = v___y_3384_;
v___y_3361_ = v___y_3385_;
v___y_3362_ = v___y_3386_;
v___y_3363_ = v___y_3387_;
v___y_3364_ = v___y_3389_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___y_3391_;
v___y_3367_ = v___y_3397_;
v___y_3368_ = v___y_3392_;
v___y_3369_ = v___y_3393_;
v___y_3370_ = v___y_3394_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3395_;
v___y_3373_ = v___x_3404_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v___y_3397_);
lean_dec(v___y_3395_);
lean_dec(v___y_3392_);
lean_dec(v___y_3390_);
lean_dec(v___y_3386_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v_a_3405_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3399_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3399_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
v___jp_3413_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Syntax_getOptional_x3f(v___y_3417_);
lean_dec(v___y_3417_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_box(0);
v___y_3384_ = v___y_3423_;
v___y_3385_ = v___y_3427_;
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3416_;
v___y_3388_ = v___y_3426_;
v___y_3389_ = v___y_3425_;
v___y_3390_ = v_args_3419_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3415_;
v___y_3393_ = v___y_3422_;
v___y_3394_ = v___y_3424_;
v___y_3395_ = v___y_3418_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___x_3429_;
goto v___jp_3383_;
}
else
{
lean_object* v_val_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_val_3430_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3428_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_val_3430_);
lean_dec(v___x_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_val_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
v___y_3384_ = v___y_3423_;
v___y_3385_ = v___y_3427_;
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3416_;
v___y_3388_ = v___y_3426_;
v___y_3389_ = v___y_3425_;
v___y_3390_ = v_args_3419_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3415_;
v___y_3393_ = v___y_3422_;
v___y_3394_ = v___y_3424_;
v___y_3395_ = v___y_3418_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___x_3435_;
goto v___jp_3383_;
}
}
}
}
v___jp_3439_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3454_ = lean_unsigned_to_nat(3u);
v___x_3455_ = l_Lean_Syntax_getArg(v___y_3442_, v___x_3454_);
lean_dec(v___y_3442_);
v___x_3456_ = l_Lean_Syntax_isNone(v___x_3455_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
lean_inc(v___x_3455_);
v___x_3457_ = l_Lean_Syntax_matchesNull(v___x_3455_, v___x_3438_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec(v___x_3455_);
lean_dec(v_o_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3459_ = l_Lean_Syntax_getArg(v___x_3455_, v___x_2507_);
lean_dec(v___x_3455_);
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3461_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3460_);
lean_inc(v___x_3459_);
v___x_3462_ = l_Lean_Syntax_isOfKind(v___x_3459_, v___x_3461_);
lean_dec(v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec(v___x_3459_);
lean_dec(v_o_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v_args_3465_; lean_object* v___x_3466_; 
v___x_3464_ = l_Lean_Syntax_getArg(v___x_3459_, v___x_3438_);
lean_dec(v___x_3459_);
v_args_3465_ = l_Lean_Syntax_getArgs(v___x_3464_);
lean_dec(v___x_3464_);
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_args_3465_);
v___y_3414_ = v___y_3440_;
v___y_3415_ = v___y_3441_;
v___y_3416_ = v___y_3443_;
v___y_3417_ = v___y_3444_;
v___y_3418_ = v_o_3445_;
v_args_3419_ = v___x_3466_;
v___y_3420_ = v___y_3446_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
v___y_3426_ = v___y_3452_;
v___y_3427_ = v___y_3453_;
goto v___jp_3413_;
}
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v___x_3455_);
v___x_3467_ = lean_box(0);
v___y_3414_ = v___y_3440_;
v___y_3415_ = v___y_3441_;
v___y_3416_ = v___y_3443_;
v___y_3417_ = v___y_3444_;
v___y_3418_ = v_o_3445_;
v_args_3419_ = v___x_3467_;
v___y_3420_ = v___y_3446_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
v___y_3426_ = v___y_3452_;
v___y_3427_ = v___y_3453_;
goto v___jp_3413_;
}
}
v___jp_3468_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3478_ = lean_unsigned_to_nat(2u);
v___x_3479_ = l_Lean_Syntax_getArg(v_stx_2491_, v___x_3478_);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3481_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3480_);
lean_inc(v___x_3479_);
v___x_3482_ = l_Lean_Syntax_isOfKind(v___x_3479_, v___x_3481_);
lean_dec(v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec(v___x_3479_);
lean_dec(v_bang_3469_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3483_;
}
else
{
lean_object* v_cfg_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v_cfg_3484_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_2507_);
v___x_3485_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
lean_inc_ref(v___x_2493_);
v___x_3486_ = l_Lean_Name_mkStr4(v___x_2493_, v___x_2494_, v___x_2495_, v___x_3485_);
lean_inc(v_cfg_3484_);
v___x_3487_ = l_Lean_Syntax_isOfKind(v_cfg_3484_, v___x_3486_);
lean_dec(v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v_cfg_3484_);
lean_dec(v___x_3479_);
lean_dec(v_bang_3469_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3488_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3489_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3438_);
v___x_3490_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3478_);
v___x_3491_ = l_Lean_Syntax_isNone(v___x_3490_);
if (v___x_3491_ == 0)
{
uint8_t v___x_3492_; 
lean_inc(v___x_3490_);
v___x_3492_ = l_Lean_Syntax_matchesNull(v___x_3490_, v___x_3438_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v___x_3490_);
lean_dec(v___x_3489_);
lean_dec(v_cfg_3484_);
lean_dec(v___x_3479_);
lean_dec(v_bang_3469_);
lean_dec(v_tk_2508_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___x_2493_);
v___x_3493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3493_;
}
else
{
lean_object* v_o_3494_; lean_object* v___x_3495_; 
v_o_3494_ = l_Lean_Syntax_getArg(v___x_3490_, v___x_2507_);
lean_dec(v___x_3490_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_o_3494_);
v___y_3440_ = v_cfg_3484_;
v___y_3441_ = v_bang_3469_;
v___y_3442_ = v___x_3479_;
v___y_3443_ = v___x_3482_;
v___y_3444_ = v___x_3489_;
v_o_3445_ = v___x_3495_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
v___y_3452_ = v___y_3476_;
v___y_3453_ = v___y_3477_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3496_; 
lean_dec(v___x_3490_);
v___x_3496_ = lean_box(0);
v___y_3440_ = v_cfg_3484_;
v___y_3441_ = v_bang_3469_;
v___y_3442_ = v___x_3479_;
v___y_3443_ = v___x_3482_;
v___y_3444_ = v___x_3489_;
v_o_3445_ = v___x_3496_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
v___y_3452_ = v___y_3476_;
v___y_3453_ = v___y_3477_;
goto v___jp_3439_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3504_, lean_object* v_stx_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v___x_3508_, lean_object* v___x_3509_, lean_object* v___f_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
uint8_t v___x_31073__boxed_3520_; uint8_t v___x_31074__boxed_3521_; lean_object* v_res_3522_; 
v___x_31073__boxed_3520_ = lean_unbox(v___x_3504_);
v___x_31074__boxed_3521_ = lean_unbox(v___x_3506_);
v_res_3522_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31073__boxed_3520_, v_stx_3505_, v___x_31074__boxed_3521_, v___x_3507_, v___x_3508_, v___x_3509_, v___f_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v_stx_3505_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; uint8_t v___x_3544_; lean_object* v___f_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___y_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3529_);
v___x_3543_ = l_Lean_Syntax_isOfKind(v_stx_3529_, v___x_3542_);
v___x_3544_ = 1;
v___f_3545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3546_ = lean_box(v___x_3543_);
v___x_3547_ = lean_box(v___x_3544_);
v___y_3548_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3548_, 0, v___x_3546_);
lean_closure_set(v___y_3548_, 1, v_stx_3529_);
lean_closure_set(v___y_3548_, 2, v___x_3547_);
lean_closure_set(v___y_3548_, 3, v___x_3539_);
lean_closure_set(v___y_3548_, 4, v___x_3540_);
lean_closure_set(v___y_3548_, 5, v___x_3541_);
lean_closure_set(v___y_3548_, 6, v___f_3545_);
v___x_3549_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3549_, 0, v___y_3548_);
v___x_3550_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3549_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3562_, lean_object* v_as_3563_, lean_object* v_as_x27_3564_, lean_object* v_b_3565_, lean_object* v_a_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3562_, v_as_x27_3564_, v_b_3565_, v___y_3573_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3577_, lean_object* v_as_3578_, lean_object* v_as_x27_3579_, lean_object* v_b_3580_, lean_object* v_a_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3577_, v_as_3578_, v_as_x27_3579_, v_b_3580_, v_a_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v_as_x27_3579_);
lean_dec(v_as_3578_);
lean_dec(v___x_3577_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3599_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3602_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3603_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3599_, v___x_3600_, v___x_3601_, v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3633_ = l_Lean_addBuiltinDeclarationRanges(v___x_3631_, v___x_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3636_, lean_object* v_simprocs_3637_, lean_object* v_fvarIdsToSimp_3638_, uint8_t v_simplifyTarget_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = lean_unsigned_to_nat(32u);
v___x_3649_ = lean_mk_empty_array_with_capacity(v___x_3648_);
lean_dec_ref(v___x_3649_);
v___x_3650_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3651_ = l_Lean_Meta_dsimpGoal(v_a_3647_, v_ctx_3636_, v_simprocs_3637_, v_simplifyTarget_3639_, v_fvarIdsToSimp_3638_, v___x_3650_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v_fst_3653_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v_fst_3653_ = lean_ctor_get(v_a_3652_, 0);
if (lean_obj_tag(v_fst_3653_) == 0)
{
lean_object* v_snd_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_snd_3654_ = lean_ctor_get(v_a_3652_, 1);
lean_inc(v_snd_3654_);
lean_dec(v_a_3652_);
v___x_3655_ = lean_box(0);
v___x_3656_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3655_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v___x_3656_, 0);
lean_dec(v_unused_3664_);
v___x_3658_ = v___x_3656_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_dec(v___x_3656_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v_snd_3654_);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_snd_3654_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v_snd_3654_);
v_a_3665_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3656_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3656_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_snd_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3699_; 
lean_inc_ref(v_fst_3653_);
v_snd_3673_ = lean_ctor_get(v_a_3652_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_a_3652_, 0);
lean_dec(v_unused_3700_);
v___x_3675_ = v_a_3652_;
v_isShared_3676_ = v_isSharedCheck_3699_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_snd_3673_);
lean_dec(v_a_3652_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3699_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_val_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v_val_3677_ = lean_ctor_get(v_fst_3653_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_fst_3653_, 1);
v___x_3678_ = lean_box(0);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 1);
lean_ctor_set(v___x_3675_, 1, v___x_3678_);
lean_ctor_set(v___x_3675_, 0, v_val_3677_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_val_3677_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3680_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___x_3681_, 0);
lean_dec(v_unused_3689_);
v___x_3683_ = v___x_3681_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v___x_3681_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_snd_3673_);
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_snd_3673_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v_snd_3673_);
v_a_3690_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3681_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3681_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_a_3701_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3651_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3651_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v_fvarIdsToSimp_3638_);
lean_dec_ref(v_simprocs_3637_);
lean_dec_ref(v_ctx_3636_);
v_a_3709_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3646_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3646_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3717_, lean_object* v_simprocs_3718_, lean_object* v_fvarIdsToSimp_3719_, lean_object* v_simplifyTarget_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
uint8_t v_simplifyTarget_boxed_3727_; lean_object* v_res_3728_; 
v_simplifyTarget_boxed_3727_ = lean_unbox(v_simplifyTarget_3720_);
v_res_3728_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3717_, v_simprocs_3718_, v_fvarIdsToSimp_3719_, v_simplifyTarget_boxed_3727_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_a_3721_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3729_, lean_object* v_simprocs_3730_, lean_object* v_fvarIdsToSimp_3731_, uint8_t v_simplifyTarget_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3729_, v_simprocs_3730_, v_fvarIdsToSimp_3731_, v_simplifyTarget_3732_, v_a_3734_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3743_, lean_object* v_simprocs_3744_, lean_object* v_fvarIdsToSimp_3745_, lean_object* v_simplifyTarget_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
uint8_t v_simplifyTarget_boxed_3756_; lean_object* v_res_3757_; 
v_simplifyTarget_boxed_3756_ = lean_unbox(v_simplifyTarget_3746_);
v_res_3757_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3743_, v_simprocs_3744_, v_fvarIdsToSimp_3745_, v_simplifyTarget_boxed_3756_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
lean_dec(v_a_3754_);
lean_dec_ref(v_a_3753_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3758_, lean_object* v_simprocs_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3761_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___x_3771_ = l_Lean_MVarId_getNondepPropHyps(v_a_3770_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = 1;
v___x_3774_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3758_, v_simprocs_3759_, v_a_3772_, v___x_3773_, v___y_3761_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3774_;
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_simprocs_3759_);
lean_dec_ref(v_ctx_3758_);
v_a_3775_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3771_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3771_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_simprocs_3759_);
lean_dec_ref(v_ctx_3758_);
v_a_3783_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3769_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3769_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3791_, lean_object* v_simprocs_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3791_, v_simprocs_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3803_, lean_object* v_ctx_3804_, lean_object* v_simprocs_3805_, uint8_t v_type_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3803_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3804_, v_simprocs_3805_, v_a_3817_, v_type_3806_, v___y_3808_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
return v___x_3818_;
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_simprocs_3805_);
lean_dec_ref(v_ctx_3804_);
v_a_3819_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3816_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3816_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3827_, lean_object* v_ctx_3828_, lean_object* v_simprocs_3829_, lean_object* v_type_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
uint8_t v_type_555__boxed_3840_; lean_object* v_res_3841_; 
v_type_555__boxed_3840_ = lean_unbox(v_type_3830_);
v_res_3841_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3827_, v_ctx_3828_, v_simprocs_3829_, v_type_555__boxed_3840_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3842_, lean_object* v_simprocs_3843_, lean_object* v_loc_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
if (lean_obj_tag(v_loc_3844_) == 0)
{
lean_object* v___f_3854_; lean_object* v___x_3855_; 
v___f_3854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3854_, 0, v_ctx_3842_);
lean_closure_set(v___f_3854_, 1, v_simprocs_3843_);
v___x_3855_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3854_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
return v___x_3855_;
}
else
{
lean_object* v_hypotheses_3856_; uint8_t v_type_3857_; lean_object* v___x_3858_; lean_object* v___f_3859_; lean_object* v___x_3860_; 
v_hypotheses_3856_ = lean_ctor_get(v_loc_3844_, 0);
lean_inc_ref(v_hypotheses_3856_);
v_type_3857_ = lean_ctor_get_uint8(v_loc_3844_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3844_, 1);
v___x_3858_ = lean_box(v_type_3857_);
v___f_3859_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3859_, 0, v_hypotheses_3856_);
lean_closure_set(v___f_3859_, 1, v_ctx_3842_);
lean_closure_set(v___f_3859_, 2, v_simprocs_3843_);
lean_closure_set(v___f_3859_, 3, v___x_3858_);
v___x_3860_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3859_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3861_, lean_object* v_simprocs_3862_, lean_object* v_loc_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3861_, v_simprocs_3862_, v_loc_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3878_, lean_object* v_stx_3879_, uint8_t v___x_3880_, lean_object* v___x_3881_, lean_object* v___x_3882_, lean_object* v___x_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
if (v___x_3878_ == 0)
{
lean_object* v___x_3893_; 
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_3893_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v_tk_3895_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v_stx_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; uint8_t v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; uint8_t v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; uint8_t v___y_4198_; lean_object* v___y_4199_; uint8_t v___y_4200_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; uint8_t v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; uint8_t v___y_4253_; lean_object* v___y_4254_; lean_object* v_args_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___x_4276_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; uint8_t v___y_4281_; lean_object* v___y_4282_; lean_object* v_o_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v_bang_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_3894_ = lean_unsigned_to_nat(0u);
v_tk_3895_ = l_Lean_Syntax_getArg(v_stx_3879_, v___x_3894_);
v___x_4276_ = lean_unsigned_to_nat(1u);
v___x_4333_ = l_Lean_Syntax_getArg(v_stx_3879_, v___x_4276_);
v___x_4334_ = l_Lean_Syntax_isNone(v___x_4333_);
if (v___x_4334_ == 0)
{
uint8_t v___x_4335_; 
lean_inc(v___x_4333_);
v___x_4335_ = l_Lean_Syntax_matchesNull(v___x_4333_, v___x_4276_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; 
lean_dec(v___x_4333_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4336_;
}
else
{
lean_object* v_bang_4337_; lean_object* v___x_4338_; 
v_bang_4337_ = l_Lean_Syntax_getArg(v___x_4333_, v___x_3894_);
lean_dec(v___x_4333_);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v_bang_4337_);
v_bang_4306_ = v___x_4338_;
v___y_4307_ = v___y_3884_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
v___y_4313_ = v___y_3890_;
v___y_4314_ = v___y_3891_;
goto v___jp_4305_;
}
}
else
{
lean_object* v___x_4339_; 
lean_dec(v___x_4333_);
v___x_4339_ = lean_box(0);
v_bang_4306_ = v___x_4339_;
v___y_4307_ = v___y_3884_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
v___y_4313_ = v___y_3890_;
v___y_4314_ = v___y_3891_;
goto v___jp_4305_;
}
v___jp_3896_:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3907_, v___y_3900_, v___y_3908_, v___y_3902_, v___y_3899_, v___y_3898_, v___y_3904_, v___y_3906_, v___y_3897_, v___y_3903_, v___y_3901_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v_usedTheorems_3911_; lean_object* v_diag_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3954_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v_usedTheorems_3911_ = lean_ctor_get(v_a_3910_, 0);
v_diag_3912_ = lean_ctor_get(v_a_3910_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3910_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3914_ = v_a_3910_;
v_isShared_3915_ = v_isSharedCheck_3954_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_diag_3912_);
lean_inc(v_usedTheorems_3911_);
lean_dec(v_a_3910_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3954_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3905_, v_usedTheorems_3911_, v___y_3906_, v___y_3897_, v___y_3903_, v___y_3901_);
lean_dec_ref(v_usedTheorems_3911_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_ref_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v_ref_3918_ = lean_ctor_get(v___y_3903_, 2);
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v_a_3917_);
lean_ctor_set(v___x_3914_, 0, v___x_3919_);
v___x_3921_ = v___x_3914_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_a_3917_);
v___x_3921_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3922_ = lean_box(0);
v___x_3923_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
lean_ctor_set(v___x_3923_, 2, v___x_3922_);
lean_ctor_set(v___x_3923_, 3, v___x_3922_);
lean_ctor_set(v___x_3923_, 4, v___x_3922_);
lean_ctor_set(v___x_3923_, 5, v___x_3922_);
lean_inc(v_ref_3918_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v_ref_3918_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3926_ = 4;
v___x_3927_ = l_Lean_MessageData_nil;
v___x_3928_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3895_, v___x_3923_, v___x_3924_, v___x_3925_, v___x_3922_, v___x_3926_, v___x_3927_, v___y_3903_, v___y_3901_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v___x_3928_, 0);
lean_dec(v_unused_3936_);
v___x_3930_ = v___x_3928_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_dec(v___x_3928_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v_diag_3912_);
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_diag_3912_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec_ref(v_diag_3912_);
v_a_3937_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3928_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3928_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_del_object(v___x_3914_);
lean_dec_ref(v_diag_3912_);
lean_dec(v_tk_3895_);
v_a_3946_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3916_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3916_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v___y_3905_);
lean_dec(v_tk_3895_);
v_a_3955_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3909_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3909_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
v___jp_3963_:
{
if (lean_obj_tag(v___y_3968_) == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3977_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*1, v___x_3880_);
v___y_3897_ = v___y_3965_;
v___y_3898_ = v___y_3964_;
v___y_3899_ = v___y_3967_;
v___y_3900_ = v___y_3966_;
v___y_3901_ = v___y_3970_;
v___y_3902_ = v___y_3969_;
v___y_3903_ = v___y_3971_;
v___y_3904_ = v___y_3972_;
v___y_3905_ = v___y_3974_;
v___y_3906_ = v___y_3973_;
v___y_3907_ = v___y_3975_;
v___y_3908_ = v___x_3977_;
goto v___jp_3896_;
}
else
{
lean_object* v_val_3978_; lean_object* v___x_3979_; 
v_val_3978_ = lean_ctor_get(v___y_3968_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v___y_3968_, 1);
v___x_3979_ = l_Lean_Elab_Tactic_expandLocation(v_val_3978_);
lean_dec(v_val_3978_);
v___y_3897_ = v___y_3965_;
v___y_3898_ = v___y_3964_;
v___y_3899_ = v___y_3967_;
v___y_3900_ = v___y_3966_;
v___y_3901_ = v___y_3970_;
v___y_3902_ = v___y_3969_;
v___y_3903_ = v___y_3971_;
v___y_3904_ = v___y_3972_;
v___y_3905_ = v___y_3974_;
v___y_3906_ = v___y_3973_;
v___y_3907_ = v___y_3975_;
v___y_3908_ = v___x_3979_;
goto v___jp_3896_;
}
}
v___jp_3980_:
{
uint8_t v___x_3993_; uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3993_ = 0;
v___x_3994_ = 2;
v___x_3995_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3996_ = lean_box(v___x_3993_);
v___x_3997_ = lean_box(v___x_3994_);
v___x_3998_ = lean_box(v___x_3993_);
lean_inc(v_stx_3984_);
v___x_3999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3999_, 0, v_stx_3984_);
lean_closure_set(v___x_3999_, 1, v___x_3996_);
lean_closure_set(v___x_3999_, 2, v___x_3997_);
lean_closure_set(v___x_3999_, 3, v___x_3998_);
lean_closure_set(v___x_3999_, 4, v___x_3995_);
v___x_4000_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3999_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
if (lean_obj_tag(v___y_3981_) == 0)
{
lean_object* v_ctx_4002_; lean_object* v_simprocs_4003_; 
v_ctx_4002_ = lean_ctor_get(v_a_4001_, 0);
lean_inc_ref(v_ctx_4002_);
v_simprocs_4003_ = lean_ctor_get(v_a_4001_, 1);
lean_inc_ref(v_simprocs_4003_);
lean_dec(v_a_4001_);
v___y_3964_ = v___y_3987_;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v_simprocs_4003_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___y_3985_;
v___y_3970_ = v___y_3992_;
v___y_3971_ = v___y_3991_;
v___y_3972_ = v___y_3988_;
v___y_3973_ = v___y_3989_;
v___y_3974_ = v_stx_3984_;
v___y_3975_ = v_ctx_4002_;
goto v___jp_3963_;
}
else
{
lean_dec_ref_known(v___y_3981_, 1);
if (v___y_3983_ == 0)
{
lean_object* v_ctx_4004_; lean_object* v_simprocs_4005_; 
v_ctx_4004_ = lean_ctor_get(v_a_4001_, 0);
lean_inc_ref(v_ctx_4004_);
v_simprocs_4005_ = lean_ctor_get(v_a_4001_, 1);
lean_inc_ref(v_simprocs_4005_);
lean_dec(v_a_4001_);
v___y_3964_ = v___y_3987_;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v_simprocs_4005_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___y_3985_;
v___y_3970_ = v___y_3992_;
v___y_3971_ = v___y_3991_;
v___y_3972_ = v___y_3988_;
v___y_3973_ = v___y_3989_;
v___y_3974_ = v_stx_3984_;
v___y_3975_ = v_ctx_4004_;
goto v___jp_3963_;
}
else
{
lean_object* v_ctx_4006_; lean_object* v_simprocs_4007_; lean_object* v___x_4008_; 
v_ctx_4006_ = lean_ctor_get(v_a_4001_, 0);
lean_inc_ref(v_ctx_4006_);
v_simprocs_4007_ = lean_ctor_get(v_a_4001_, 1);
lean_inc_ref(v_simprocs_4007_);
lean_dec(v_a_4001_);
v___x_4008_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4006_);
v___y_3964_ = v___y_3987_;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v_simprocs_4007_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___y_3985_;
v___y_3970_ = v___y_3992_;
v___y_3971_ = v___y_3991_;
v___y_3972_ = v___y_3988_;
v___y_3973_ = v___y_3989_;
v___y_3974_ = v_stx_3984_;
v___y_3975_ = v___x_4008_;
goto v___jp_3963_;
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_stx_3984_);
lean_dec(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec(v_tk_3895_);
v_a_4009_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4000_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4000_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
v___jp_4017_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_inc_ref(v___y_4024_);
v___x_4039_ = l_Array_append___redArg(v___y_4024_, v___y_4038_);
lean_dec_ref(v___y_4038_);
lean_inc(v___y_4037_);
lean_inc(v___y_4032_);
v___x_4040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4032_);
lean_ctor_set(v___x_4040_, 1, v___y_4037_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
v___x_4041_ = l_Lean_Syntax_node6(v___y_4032_, v___y_4029_, v___y_4033_, v___y_4030_, v___y_4021_, v___y_4026_, v___y_4020_, v___x_4040_);
v___y_3981_ = v___y_4019_;
v___y_3982_ = v___y_4031_;
v___y_3983_ = v___y_4035_;
v_stx_3984_ = v___x_4041_;
v___y_3985_ = v___y_4022_;
v___y_3986_ = v___y_4028_;
v___y_3987_ = v___y_4034_;
v___y_3988_ = v___y_4025_;
v___y_3989_ = v___y_4018_;
v___y_3990_ = v___y_4036_;
v___y_3991_ = v___y_4027_;
v___y_3992_ = v___y_4023_;
goto v___jp_3980_;
}
v___jp_4042_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
lean_inc_ref(v___y_4047_);
v___x_4063_ = l_Array_append___redArg(v___y_4047_, v___y_4062_);
lean_dec_ref(v___y_4062_);
lean_inc(v___y_4061_);
lean_inc(v___y_4058_);
v___x_4064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4064_, 0, v___y_4058_);
lean_ctor_set(v___x_4064_, 1, v___y_4061_);
lean_ctor_set(v___x_4064_, 2, v___x_4063_);
if (lean_obj_tag(v___y_4055_) == 0)
{
lean_object* v___x_4065_; 
v___x_4065_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4018_ = v___y_4043_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___x_4064_;
v___y_4021_ = v___y_4045_;
v___y_4022_ = v___y_4046_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4047_;
v___y_4025_ = v___y_4049_;
v___y_4026_ = v___y_4050_;
v___y_4027_ = v___y_4051_;
v___y_4028_ = v___y_4052_;
v___y_4029_ = v___y_4053_;
v___y_4030_ = v___y_4054_;
v___y_4031_ = v___y_4055_;
v___y_4032_ = v___y_4058_;
v___y_4033_ = v___y_4057_;
v___y_4034_ = v___y_4056_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4060_;
v___y_4037_ = v___y_4061_;
v___y_4038_ = v___x_4065_;
goto v___jp_4017_;
}
else
{
lean_object* v_val_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v_val_4066_ = lean_ctor_get(v___y_4055_, 0);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4066_);
v___x_4068_ = lean_array_push(v___x_4067_, v_val_4066_);
v___y_4018_ = v___y_4043_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___x_4064_;
v___y_4021_ = v___y_4045_;
v___y_4022_ = v___y_4046_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4047_;
v___y_4025_ = v___y_4049_;
v___y_4026_ = v___y_4050_;
v___y_4027_ = v___y_4051_;
v___y_4028_ = v___y_4052_;
v___y_4029_ = v___y_4053_;
v___y_4030_ = v___y_4054_;
v___y_4031_ = v___y_4055_;
v___y_4032_ = v___y_4058_;
v___y_4033_ = v___y_4057_;
v___y_4034_ = v___y_4056_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4060_;
v___y_4037_ = v___y_4061_;
v___y_4038_ = v___x_4068_;
goto v___jp_4017_;
}
}
v___jp_4069_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
lean_inc_ref(v___y_4074_);
v___x_4090_ = l_Array_append___redArg(v___y_4074_, v___y_4089_);
lean_dec_ref(v___y_4089_);
lean_inc(v___y_4088_);
lean_inc(v___y_4084_);
v___x_4091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4091_, 0, v___y_4084_);
lean_ctor_set(v___x_4091_, 1, v___y_4088_);
lean_ctor_set(v___x_4091_, 2, v___x_4090_);
if (lean_obj_tag(v___y_4085_) == 1)
{
lean_object* v_val_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_val_4092_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_val_4092_);
lean_dec_ref_known(v___y_4085_, 1);
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4084_, 3);
v___x_4094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___y_4084_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
lean_inc_ref(v___y_4074_);
v___x_4095_ = l_Array_append___redArg(v___y_4074_, v_val_4092_);
lean_dec(v_val_4092_);
lean_inc(v___y_4088_);
v___x_4096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4096_, 0, v___y_4084_);
lean_ctor_set(v___x_4096_, 1, v___y_4088_);
lean_ctor_set(v___x_4096_, 2, v___x_4095_);
v___x_4097_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___y_4084_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = l_Array_mkArray3___redArg(v___x_4094_, v___x_4096_, v___x_4098_);
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4072_;
v___y_4046_ = v___y_4073_;
v___y_4047_ = v___y_4074_;
v___y_4048_ = v___y_4075_;
v___y_4049_ = v___y_4076_;
v___y_4050_ = v___x_4091_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___y_4082_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4088_;
v___y_4062_ = v___x_4099_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4100_; 
lean_dec(v___y_4085_);
v___x_4100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4072_;
v___y_4046_ = v___y_4073_;
v___y_4047_ = v___y_4074_;
v___y_4048_ = v___y_4075_;
v___y_4049_ = v___y_4076_;
v___y_4050_ = v___x_4091_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___y_4082_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4088_;
v___y_4062_ = v___x_4100_;
goto v___jp_4042_;
}
}
v___jp_4101_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_inc_ref(v___y_4109_);
v___x_4123_ = l_Array_append___redArg(v___y_4109_, v___y_4122_);
lean_dec_ref(v___y_4122_);
lean_inc(v___y_4120_);
lean_inc(v___y_4114_);
v___x_4124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4124_, 0, v___y_4114_);
lean_ctor_set(v___x_4124_, 1, v___y_4120_);
lean_ctor_set(v___x_4124_, 2, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node6(v___y_4114_, v___y_4121_, v___y_4113_, v___y_4115_, v___y_4107_, v___y_4111_, v___y_4106_, v___x_4124_);
v___y_3981_ = v___y_4103_;
v___y_3982_ = v___y_4116_;
v___y_3983_ = v___y_4118_;
v_stx_3984_ = v___x_4125_;
v___y_3985_ = v___y_4104_;
v___y_3986_ = v___y_4112_;
v___y_3987_ = v___y_4117_;
v___y_3988_ = v___y_4108_;
v___y_3989_ = v___y_4102_;
v___y_3990_ = v___y_4119_;
v___y_3991_ = v___y_4110_;
v___y_3992_ = v___y_4105_;
goto v___jp_3980_;
}
v___jp_4126_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_inc_ref(v___y_4133_);
v___x_4147_ = l_Array_append___redArg(v___y_4133_, v___y_4146_);
lean_dec_ref(v___y_4146_);
lean_inc(v___y_4144_);
lean_inc(v___y_4138_);
v___x_4148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4148_, 0, v___y_4138_);
lean_ctor_set(v___x_4148_, 1, v___y_4144_);
lean_ctor_set(v___x_4148_, 2, v___x_4147_);
if (lean_obj_tag(v___y_4140_) == 0)
{
lean_object* v___x_4149_; 
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4102_ = v___y_4127_;
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4130_;
v___y_4106_ = v___x_4148_;
v___y_4107_ = v___y_4131_;
v___y_4108_ = v___y_4132_;
v___y_4109_ = v___y_4133_;
v___y_4110_ = v___y_4134_;
v___y_4111_ = v___y_4135_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4137_;
v___y_4114_ = v___y_4138_;
v___y_4115_ = v___y_4139_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___y_4141_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___y_4144_;
v___y_4121_ = v___y_4145_;
v___y_4122_ = v___x_4149_;
goto v___jp_4101_;
}
else
{
lean_object* v_val_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_val_4150_ = lean_ctor_get(v___y_4140_, 0);
v___x_4151_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4150_);
v___x_4152_ = lean_array_push(v___x_4151_, v_val_4150_);
v___y_4102_ = v___y_4127_;
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4130_;
v___y_4106_ = v___x_4148_;
v___y_4107_ = v___y_4131_;
v___y_4108_ = v___y_4132_;
v___y_4109_ = v___y_4133_;
v___y_4110_ = v___y_4134_;
v___y_4111_ = v___y_4135_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4137_;
v___y_4114_ = v___y_4138_;
v___y_4115_ = v___y_4139_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___y_4141_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___y_4144_;
v___y_4121_ = v___y_4145_;
v___y_4122_ = v___x_4152_;
goto v___jp_4101_;
}
}
v___jp_4153_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_inc_ref(v___y_4160_);
v___x_4174_ = l_Array_append___redArg(v___y_4160_, v___y_4173_);
lean_dec_ref(v___y_4173_);
lean_inc(v___y_4171_);
lean_inc(v___y_4164_);
v___x_4175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4175_, 0, v___y_4164_);
lean_ctor_set(v___x_4175_, 1, v___y_4171_);
lean_ctor_set(v___x_4175_, 2, v___x_4174_);
if (lean_obj_tag(v___y_4168_) == 1)
{
lean_object* v_val_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_val_4176_ = lean_ctor_get(v___y_4168_, 0);
lean_inc(v_val_4176_);
lean_dec_ref_known(v___y_4168_, 1);
v___x_4177_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4164_, 3);
v___x_4178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___y_4164_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
lean_inc_ref(v___y_4160_);
v___x_4179_ = l_Array_append___redArg(v___y_4160_, v_val_4176_);
lean_dec(v_val_4176_);
lean_inc(v___y_4171_);
v___x_4180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4180_, 0, v___y_4164_);
lean_ctor_set(v___x_4180_, 1, v___y_4171_);
lean_ctor_set(v___x_4180_, 2, v___x_4179_);
v___x_4181_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___y_4164_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l_Array_mkArray3___redArg(v___x_4178_, v___x_4180_, v___x_4182_);
v___y_4127_ = v___y_4154_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___x_4175_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___y_4163_;
v___y_4138_ = v___y_4164_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4166_;
v___y_4141_ = v___y_4167_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___x_4183_;
goto v___jp_4126_;
}
else
{
lean_object* v___x_4184_; 
lean_dec(v___y_4168_);
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4127_ = v___y_4154_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___x_4175_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___y_4163_;
v___y_4138_ = v___y_4164_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4166_;
v___y_4141_ = v___y_4167_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___x_4184_;
goto v___jp_4126_;
}
}
v___jp_4185_:
{
lean_object* v_ref_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_ref_4201_ = lean_ctor_get(v___y_4192_, 2);
v___x_4202_ = l_Lean_SourceInfo_fromRef(v_ref_4201_, v___y_4200_);
v___x_4203_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4204_ = l_Lean_Name_mkStr4(v___x_3881_, v___x_3882_, v___x_3883_, v___x_4203_);
v___x_4205_ = l_Lean_SourceInfo_fromRef(v_tk_3895_, v___x_3880_);
v___x_4206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v___x_4203_);
v___x_4207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4208_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4202_);
v___x_4209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4202_);
lean_ctor_set(v___x_4209_, 1, v___x_4207_);
lean_ctor_set(v___x_4209_, 2, v___x_4208_);
if (lean_obj_tag(v___y_4188_) == 1)
{
lean_object* v_val_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_val_4210_ = lean_ctor_get(v___y_4188_, 0);
lean_inc(v_val_4210_);
lean_dec_ref_known(v___y_4188_, 1);
v___x_4211_ = l_Lean_SourceInfo_fromRef(v_val_4210_, v___x_3880_);
lean_dec(v_val_4210_);
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = l_Array_mkArray1___redArg(v___x_4213_);
v___y_4070_ = v___y_4186_;
v___y_4071_ = v___y_4187_;
v___y_4072_ = v___x_4209_;
v___y_4073_ = v___y_4189_;
v___y_4074_ = v___x_4208_;
v___y_4075_ = v___y_4190_;
v___y_4076_ = v___y_4191_;
v___y_4077_ = v___y_4192_;
v___y_4078_ = v___y_4193_;
v___y_4079_ = v___x_4204_;
v___y_4080_ = v___y_4194_;
v___y_4081_ = v___y_4195_;
v___y_4082_ = v___x_4206_;
v___y_4083_ = v___y_4196_;
v___y_4084_ = v___x_4202_;
v___y_4085_ = v___y_4197_;
v___y_4086_ = v___y_4198_;
v___y_4087_ = v___y_4199_;
v___y_4088_ = v___x_4207_;
v___y_4089_ = v___x_4214_;
goto v___jp_4069_;
}
else
{
lean_object* v___x_4215_; 
lean_dec(v___y_4188_);
v___x_4215_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4070_ = v___y_4186_;
v___y_4071_ = v___y_4187_;
v___y_4072_ = v___x_4209_;
v___y_4073_ = v___y_4189_;
v___y_4074_ = v___x_4208_;
v___y_4075_ = v___y_4190_;
v___y_4076_ = v___y_4191_;
v___y_4077_ = v___y_4192_;
v___y_4078_ = v___y_4193_;
v___y_4079_ = v___x_4204_;
v___y_4080_ = v___y_4194_;
v___y_4081_ = v___y_4195_;
v___y_4082_ = v___x_4206_;
v___y_4083_ = v___y_4196_;
v___y_4084_ = v___x_4202_;
v___y_4085_ = v___y_4197_;
v___y_4086_ = v___y_4198_;
v___y_4087_ = v___y_4199_;
v___y_4088_ = v___x_4207_;
v___y_4089_ = v___x_4215_;
goto v___jp_4069_;
}
}
v___jp_4216_:
{
if (lean_obj_tag(v___y_4218_) == 0)
{
uint8_t v___x_4231_; 
v___x_4231_ = 0;
v___y_4186_ = v___y_4217_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4230_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4227_;
v___y_4199_ = v___y_4229_;
v___y_4200_ = v___x_4231_;
goto v___jp_4185_;
}
else
{
if (v___y_4227_ == 0)
{
v___y_4186_ = v___y_4217_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4230_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4227_;
v___y_4199_ = v___y_4229_;
v___y_4200_ = v___y_4227_;
goto v___jp_4185_;
}
else
{
lean_object* v_ref_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_ref_4232_ = lean_ctor_get(v___y_4223_, 2);
v___x_4233_ = 0;
v___x_4234_ = l_Lean_SourceInfo_fromRef(v_ref_4232_, v___x_4233_);
v___x_4235_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4236_ = l_Lean_Name_mkStr4(v___x_3881_, v___x_3882_, v___x_3883_, v___x_4235_);
v___x_4237_ = l_Lean_SourceInfo_fromRef(v_tk_3895_, v___x_3880_);
v___x_4238_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4241_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4234_);
v___x_4242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4234_);
lean_ctor_set(v___x_4242_, 1, v___x_4240_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
if (lean_obj_tag(v___y_4219_) == 1)
{
lean_object* v_val_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v_val_4243_ = lean_ctor_get(v___y_4219_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v___y_4219_, 1);
v___x_4244_ = l_Lean_SourceInfo_fromRef(v_val_4243_, v___x_3880_);
lean_dec(v_val_4243_);
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Array_mkArray1___redArg(v___x_4246_);
v___y_4154_ = v___y_4217_;
v___y_4155_ = v___y_4218_;
v___y_4156_ = v___y_4220_;
v___y_4157_ = v___y_4221_;
v___y_4158_ = v___x_4242_;
v___y_4159_ = v___y_4222_;
v___y_4160_ = v___x_4241_;
v___y_4161_ = v___y_4223_;
v___y_4162_ = v___y_4224_;
v___y_4163_ = v___x_4239_;
v___y_4164_ = v___x_4234_;
v___y_4165_ = v___y_4225_;
v___y_4166_ = v___y_4230_;
v___y_4167_ = v___y_4226_;
v___y_4168_ = v___y_4228_;
v___y_4169_ = v___y_4227_;
v___y_4170_ = v___y_4229_;
v___y_4171_ = v___x_4240_;
v___y_4172_ = v___x_4236_;
v___y_4173_ = v___x_4247_;
goto v___jp_4153_;
}
else
{
lean_object* v___x_4248_; 
lean_dec(v___y_4219_);
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4154_ = v___y_4217_;
v___y_4155_ = v___y_4218_;
v___y_4156_ = v___y_4220_;
v___y_4157_ = v___y_4221_;
v___y_4158_ = v___x_4242_;
v___y_4159_ = v___y_4222_;
v___y_4160_ = v___x_4241_;
v___y_4161_ = v___y_4223_;
v___y_4162_ = v___y_4224_;
v___y_4163_ = v___x_4239_;
v___y_4164_ = v___x_4234_;
v___y_4165_ = v___y_4225_;
v___y_4166_ = v___y_4230_;
v___y_4167_ = v___y_4226_;
v___y_4168_ = v___y_4228_;
v___y_4169_ = v___y_4227_;
v___y_4170_ = v___y_4229_;
v___y_4171_ = v___x_4240_;
v___y_4172_ = v___x_4236_;
v___y_4173_ = v___x_4248_;
goto v___jp_4153_;
}
}
}
}
v___jp_4249_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_unsigned_to_nat(3u);
v___x_4265_ = l_Lean_Syntax_getArg(v___y_4254_, v___x_4264_);
lean_dec(v___y_4254_);
v___x_4266_ = l_Lean_Syntax_getOptional_x3f(v___x_4265_);
lean_dec(v___x_4265_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_box(0);
v___y_4217_ = v___y_4260_;
v___y_4218_ = v___y_4250_;
v___y_4219_ = v___y_4252_;
v___y_4220_ = v___y_4256_;
v___y_4221_ = v___y_4263_;
v___y_4222_ = v___y_4259_;
v___y_4223_ = v___y_4262_;
v___y_4224_ = v___y_4257_;
v___y_4225_ = v___y_4251_;
v___y_4226_ = v___y_4258_;
v___y_4227_ = v___y_4253_;
v___y_4228_ = v_args_4255_;
v___y_4229_ = v___y_4261_;
v___y_4230_ = v___x_4267_;
goto v___jp_4216_;
}
else
{
lean_object* v_val_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
v_val_4268_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4266_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_val_4268_);
lean_dec(v___x_4266_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_val_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
v___y_4217_ = v___y_4260_;
v___y_4218_ = v___y_4250_;
v___y_4219_ = v___y_4252_;
v___y_4220_ = v___y_4256_;
v___y_4221_ = v___y_4263_;
v___y_4222_ = v___y_4259_;
v___y_4223_ = v___y_4262_;
v___y_4224_ = v___y_4257_;
v___y_4225_ = v___y_4251_;
v___y_4226_ = v___y_4258_;
v___y_4227_ = v___y_4253_;
v___y_4228_ = v_args_4255_;
v___y_4229_ = v___y_4261_;
v___y_4230_ = v___x_4273_;
goto v___jp_4216_;
}
}
}
}
v___jp_4277_:
{
lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4292_ = l_Lean_Syntax_getArg(v___y_4282_, v___y_4280_);
v___x_4293_ = l_Lean_Syntax_isNone(v___x_4292_);
if (v___x_4293_ == 0)
{
uint8_t v___x_4294_; 
lean_inc(v___x_4292_);
v___x_4294_ = l_Lean_Syntax_matchesNull(v___x_4292_, v___x_4276_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; 
lean_dec(v___x_4292_);
lean_dec(v_o_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4296_ = l_Lean_Syntax_getArg(v___x_4292_, v___x_3894_);
lean_dec(v___x_4292_);
v___x_4297_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
lean_inc_ref(v___x_3881_);
v___x_4298_ = l_Lean_Name_mkStr4(v___x_3881_, v___x_3882_, v___x_3883_, v___x_4297_);
lean_inc(v___x_4296_);
v___x_4299_ = l_Lean_Syntax_isOfKind(v___x_4296_, v___x_4298_);
lean_dec(v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; 
lean_dec(v___x_4296_);
lean_dec(v_o_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4300_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; lean_object* v_args_4302_; lean_object* v___x_4303_; 
v___x_4301_ = l_Lean_Syntax_getArg(v___x_4296_, v___x_4276_);
lean_dec(v___x_4296_);
v_args_4302_ = l_Lean_Syntax_getArgs(v___x_4301_);
lean_dec(v___x_4301_);
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_args_4302_);
v___y_4250_ = v___y_4278_;
v___y_4251_ = v___y_4279_;
v___y_4252_ = v_o_4283_;
v___y_4253_ = v___y_4281_;
v___y_4254_ = v___y_4282_;
v_args_4255_ = v___x_4303_;
v___y_4256_ = v___y_4284_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v___y_4262_ = v___y_4290_;
v___y_4263_ = v___y_4291_;
goto v___jp_4249_;
}
}
}
else
{
lean_object* v___x_4304_; 
lean_dec(v___x_4292_);
v___x_4304_ = lean_box(0);
v___y_4250_ = v___y_4278_;
v___y_4251_ = v___y_4279_;
v___y_4252_ = v_o_4283_;
v___y_4253_ = v___y_4281_;
v___y_4254_ = v___y_4282_;
v_args_4255_ = v___x_4304_;
v___y_4256_ = v___y_4284_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v___y_4262_ = v___y_4290_;
v___y_4263_ = v___y_4291_;
goto v___jp_4249_;
}
}
v___jp_4305_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4315_ = lean_unsigned_to_nat(2u);
v___x_4316_ = l_Lean_Syntax_getArg(v_stx_3879_, v___x_4315_);
v___x_4317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
lean_inc_ref(v___x_3881_);
v___x_4318_ = l_Lean_Name_mkStr4(v___x_3881_, v___x_3882_, v___x_3883_, v___x_4317_);
lean_inc(v___x_4316_);
v___x_4319_ = l_Lean_Syntax_isOfKind(v___x_4316_, v___x_4318_);
lean_dec(v___x_4318_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; 
lean_dec(v___x_4316_);
lean_dec(v_bang_4306_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v___x_4321_ = l_Lean_Syntax_getArg(v___x_4316_, v___x_3894_);
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
lean_inc_ref(v___x_3881_);
v___x_4323_ = l_Lean_Name_mkStr4(v___x_3881_, v___x_3882_, v___x_3883_, v___x_4322_);
lean_inc(v___x_4321_);
v___x_4324_ = l_Lean_Syntax_isOfKind(v___x_4321_, v___x_4323_);
lean_dec(v___x_4323_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; 
lean_dec(v___x_4321_);
lean_dec(v___x_4316_);
lean_dec(v_bang_4306_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4325_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4325_;
}
else
{
lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4326_ = l_Lean_Syntax_getArg(v___x_4316_, v___x_4276_);
v___x_4327_ = l_Lean_Syntax_isNone(v___x_4326_);
if (v___x_4327_ == 0)
{
uint8_t v___x_4328_; 
lean_inc(v___x_4326_);
v___x_4328_ = l_Lean_Syntax_matchesNull(v___x_4326_, v___x_4276_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
lean_dec(v___x_4326_);
lean_dec(v___x_4321_);
lean_dec(v___x_4316_);
lean_dec(v_bang_4306_);
lean_dec(v_tk_3895_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3881_);
v___x_4329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4329_;
}
else
{
lean_object* v_o_4330_; lean_object* v___x_4331_; 
v_o_4330_ = l_Lean_Syntax_getArg(v___x_4326_, v___x_3894_);
lean_dec(v___x_4326_);
v___x_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4331_, 0, v_o_4330_);
v___y_4278_ = v_bang_4306_;
v___y_4279_ = v___x_4321_;
v___y_4280_ = v___x_4315_;
v___y_4281_ = v___x_4319_;
v___y_4282_ = v___x_4316_;
v_o_4283_ = v___x_4331_;
v___y_4284_ = v___y_4307_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
v___y_4290_ = v___y_4313_;
v___y_4291_ = v___y_4314_;
goto v___jp_4277_;
}
}
else
{
lean_object* v___x_4332_; 
lean_dec(v___x_4326_);
v___x_4332_ = lean_box(0);
v___y_4278_ = v_bang_4306_;
v___y_4279_ = v___x_4321_;
v___y_4280_ = v___x_4315_;
v___y_4281_ = v___x_4319_;
v___y_4282_ = v___x_4316_;
v_o_4283_ = v___x_4332_;
v___y_4284_ = v___y_4307_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
v___y_4290_ = v___y_4313_;
v___y_4291_ = v___y_4314_;
goto v___jp_4277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4340_, lean_object* v_stx_4341_, lean_object* v___x_4342_, lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v___x_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
uint8_t v___x_8035__boxed_4355_; uint8_t v___x_8036__boxed_4356_; lean_object* v_res_4357_; 
v___x_8035__boxed_4355_ = lean_unbox(v___x_4340_);
v___x_8036__boxed_4356_ = lean_unbox(v___x_4342_);
v_res_4357_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8035__boxed_4355_, v_stx_4341_, v___x_8036__boxed_4356_, v___x_4343_, v___x_4344_, v___x_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v_stx_4341_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___y_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4364_);
v___x_4378_ = l_Lean_Syntax_isOfKind(v_stx_4364_, v___x_4377_);
v___x_4379_ = 1;
v___x_4380_ = lean_box(v___x_4378_);
v___x_4381_ = lean_box(v___x_4379_);
v___y_4382_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4382_, 0, v___x_4380_);
lean_closure_set(v___y_4382_, 1, v_stx_4364_);
lean_closure_set(v___y_4382_, 2, v___x_4381_);
lean_closure_set(v___y_4382_, 3, v___x_4374_);
lean_closure_set(v___y_4382_, 4, v___x_4375_);
lean_closure_set(v___y_4382_, 5, v___x_4376_);
v___x_4383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4383_, 0, v___y_4382_);
v___x_4384_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4383_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4403_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4406_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4407_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4403_, v___x_4404_, v___x_4405_, v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4438_ = l_Lean_addBuiltinDeclarationRanges(v___x_4436_, v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4440_;
}
}
lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_SimpTrace(builtin);
}
#ifdef __cplusplus
}
#endif
