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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_dec(v_pre_51_);
lean_dec_ref_known(v_pre_50_, 2);
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
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v_pre_26_);
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
uint8_t v___x_33591__boxed_208_; lean_object* v_res_209_; 
v___x_33591__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33591__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_33618__boxed_246_; lean_object* v_res_247_; 
v___x_33618__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33618__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
uint8_t v_suppressElabErrors_boxed_382_; uint8_t v___y_33821__boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v_suppressElabErrors_boxed_382_ = lean_unbox(v_suppressElabErrors_379_);
v___y_33821__boxed_383_ = lean_unbox(v___y_380_);
v_res_384_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_382_, v___y_33821__boxed_383_, v_x_381_);
lean_dec(v_x_381_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_387_, lean_object* v_msgData_388_, uint8_t v_severity_389_, uint8_t v_isSilent_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v_toCold_404_; lean_object* v___y_405_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; uint8_t v___y_440_; lean_object* v___y_441_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; uint8_t v___y_471_; uint8_t v___y_472_; uint8_t v___y_473_; uint8_t v___x_484_; uint8_t v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; uint8_t v___y_490_; uint8_t v___x_498_; 
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
lean_ctor_set(v___x_409_, 1, v___y_400_);
lean_inc_ref(v___y_401_);
lean_inc_ref(v___y_398_);
v___x_410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_410_, 0, v___y_398_);
lean_ctor_set(v___x_410_, 1, v___y_403_);
lean_ctor_set(v___x_410_, 2, v___y_399_);
lean_ctor_set(v___x_410_, 3, v___y_401_);
lean_ctor_set(v___x_410_, 4, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5, v___y_397_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 1, v___y_402_);
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
v___x_450_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_438_);
lean_dec(v___y_438_);
v___x_451_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_441_);
lean_dec(v___y_441_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_437_ == 0)
{
lean_del_object(v___x_448_);
lean_dec_ref(v___y_435_);
v___y_397_ = v___y_436_;
v___y_398_ = v_fileName_442_;
v___y_399_ = v___x_452_;
v___y_400_ = v_a_446_;
v___y_401_ = v___x_453_;
v___y_402_ = v___y_440_;
v___y_403_ = v___x_450_;
v_toCold_404_ = v___y_434_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
else
{
uint8_t v___x_454_; 
lean_inc(v_a_446_);
v___x_454_ = l_Lean_MessageData_hasTag(v___y_435_, v_a_446_);
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
v___y_397_ = v___y_436_;
v___y_398_ = v_fileName_442_;
v___y_399_ = v___x_452_;
v___y_400_ = v_a_446_;
v___y_401_ = v___x_453_;
v___y_402_ = v___y_440_;
v___y_403_ = v___x_450_;
v_toCold_404_ = v___y_434_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Syntax_getTailPos_x3f(v___y_465_, v___y_464_);
lean_dec(v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_inc(v___y_467_);
v___y_434_ = v___y_462_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_464_;
v___y_437_ = v___y_461_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_462_;
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
v___y_434_ = v___y_462_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_464_;
v___y_437_ = v___y_461_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_462_;
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
v___y_461_ = v_suppressElabErrors_476_;
v___y_462_ = v_toCold_474_;
v___y_463_ = v___f_479_;
v___y_464_ = v___y_472_;
v___y_465_ = v_ref_480_;
v___y_466_ = v___y_473_;
v___y_467_ = v___x_482_;
goto v___jp_460_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_481_, 1);
v___y_461_ = v_suppressElabErrors_476_;
v___y_462_ = v_toCold_474_;
v___y_463_ = v___f_479_;
v___y_464_ = v___y_472_;
v___y_465_ = v_ref_480_;
v___y_466_ = v___y_473_;
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
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
lean_ctor_set(v___x_765_, 4, v___x_763_);
lean_ctor_set(v___x_765_, 5, v___x_763_);
lean_ctor_set(v___x_765_, 6, v___x_763_);
lean_ctor_set(v___x_765_, 7, v___x_763_);
lean_ctor_set(v___x_765_, 8, v___x_763_);
lean_ctor_set(v___x_765_, 9, v___x_763_);
lean_ctor_set(v___x_765_, 10, v___x_763_);
lean_ctor_set(v___x_765_, 11, v___x_762_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(32u);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_770_);
lean_ctor_set_usize(v___x_774_, 4, v___x_769_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(1);
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_800_, lean_object* v_declHint_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_env_806_; uint8_t v___x_807_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_st_ref_get(v___y_802_);
v_env_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_env_806_);
lean_dec(v___x_805_);
v___x_807_ = l_Lean_Name_isAnonymous(v_declHint_801_);
if (v___x_807_ == 0)
{
uint8_t v_isExporting_808_; 
v_isExporting_808_ = lean_ctor_get_uint8(v_env_806_, sizeof(void*)*13);
if (v_isExporting_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_env_806_);
lean_dec(v_declHint_801_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_msg_800_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
lean_inc_ref(v_env_806_);
v___x_810_ = l_Lean_Environment_setExporting(v_env_806_, v___x_807_);
lean_inc(v_declHint_801_);
lean_inc_ref(v___x_810_);
v___x_811_ = l_Lean_Environment_contains(v___x_810_, v_declHint_801_, v_isExporting_808_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v___x_810_);
lean_dec_ref(v_env_806_);
lean_dec(v_declHint_801_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_msg_800_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_c_818_; lean_object* v___x_819_; 
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_815_ = l_Lean_Options_empty;
v___x_816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_816_, 0, v___x_810_);
lean_ctor_set(v___x_816_, 1, v___x_813_);
lean_ctor_set(v___x_816_, 2, v___x_814_);
lean_ctor_set(v___x_816_, 3, v___x_815_);
lean_inc(v_declHint_801_);
v___x_817_ = l_Lean_MessageData_ofConstName(v_declHint_801_, v___x_807_);
v_c_818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_818_, 0, v___x_816_);
lean_ctor_set(v_c_818_, 1, v___x_817_);
v___x_819_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_806_, v_declHint_801_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_env_806_);
lean_dec(v_declHint_801_);
v___x_820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_c_818_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_MessageData_note(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v_msg_800_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_861_; 
v_val_827_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_861_ == 0)
{
v___x_829_ = v___x_819_;
v_isShared_830_ = v_isSharedCheck_861_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_dec(v___x_819_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_861_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_mod_833_; uint8_t v___x_834_; 
v___x_831_ = l_Lean_Environment_header(v_env_806_);
lean_dec_ref(v_env_806_);
v___x_832_ = l_Lean_EnvironmentHeader_moduleNames(v___x_831_);
v_mod_833_ = lean_array_get(v___x_804_, v___x_832_, v_val_827_);
lean_dec(v_val_827_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_isPrivateName(v_declHint_801_);
lean_dec(v_declHint_801_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_c_818_);
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_MessageData_note(v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v_msg_800_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 0);
lean_ctor_set(v___x_829_, 0, v___x_844_);
v___x_846_ = v___x_829_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_c_818_);
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_800_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 0);
lean_ctor_set(v___x_829_, 0, v___x_857_);
v___x_859_ = v___x_829_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_862_; 
lean_dec_ref(v_env_806_);
lean_dec(v_declHint_801_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_msg_800_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_863_, lean_object* v_declHint_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_863_, v_declHint_864_, v___y_865_);
lean_dec(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_868_, lean_object* v_declHint_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v___x_879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_868_, v_declHint_869_, v___y_877_);
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = l_Lean_unknownIdentifierMessageTag;
v___x_885_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_890_, v_declHint_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_902_, lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_916_; 
v___x_914_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_903_, v_declHint_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_902_, v_a_915_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_917_, lean_object* v_msg_918_, lean_object* v_declHint_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_917_, v_msg_918_, v_declHint_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v_ref_917_);
return v_res_929_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_936_, lean_object* v_constName_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_947_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_948_ = 0;
lean_inc(v_constName_937_);
v___x_949_ = l_Lean_MessageData_ofConstName(v_constName_937_, v___x_948_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_947_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_936_, v___x_952_, v_constName_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_954_, lean_object* v_constName_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_954_, v_constName_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v_ref_954_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_966_, lean_object* v_cs_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_cs_978_; uint8_t v___x_982_; 
v___x_977_ = lean_box(0);
v_cs_978_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_967_, v___x_977_);
v___x_982_ = l_List_isEmpty___redArg(v_cs_978_);
if (v___x_982_ == 0)
{
lean_dec(v_n_966_);
goto v___jp_979_;
}
else
{
lean_object* v_ref_983_; lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_cs_978_);
v_ref_983_ = lean_ctor_get(v___y_974_, 2);
v___x_984_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_983_, v_n_966_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
v___jp_979_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_978_, v___x_977_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_993_, lean_object* v_cs_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_993_, v_cs_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = 1;
lean_inc(v_n_1005_);
v___x_1016_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1005_, v___x_1015_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1005_, v_a_1017_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_n_1005_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_array_to_list(v_a_1039_);
return v___x_1040_;
}
else
{
lean_object* v_head_1041_; 
v_head_1041_ = lean_ctor_get(v_a_1038_, 0);
if (lean_obj_tag(v_head_1041_) == 1)
{
lean_object* v_fields_1042_; 
v_fields_1042_ = lean_ctor_get(v_head_1041_, 1);
if (lean_obj_tag(v_fields_1042_) == 0)
{
lean_object* v_tail_1043_; lean_object* v_n_1044_; lean_object* v___x_1045_; 
lean_inc_ref(v_head_1041_);
v_tail_1043_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_tail_1043_);
lean_dec_ref_known(v_a_1038_, 2);
v_n_1044_ = lean_ctor_get(v_head_1041_, 0);
lean_inc(v_n_1044_);
lean_dec_ref_known(v_head_1041_, 2);
v___x_1045_ = lean_array_push(v_a_1039_, v_n_1044_);
v_a_1038_ = v_tail_1043_;
v_a_1039_ = v___x_1045_;
goto _start;
}
else
{
lean_object* v_tail_1047_; 
v_tail_1047_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_tail_1047_);
lean_dec_ref_known(v_a_1038_, 2);
v_a_1038_ = v_tail_1047_;
goto _start;
}
}
else
{
lean_object* v_tail_1049_; 
v_tail_1049_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_tail_1049_);
lean_dec_ref_known(v_a_1038_, 2);
v_a_1038_ = v_tail_1049_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1057_ = l_Lean_MessageData_ofFormat(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1058_, lean_object* v_k_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
if (lean_obj_tag(v_stx_1058_) == 3)
{
lean_object* v_val_1069_; lean_object* v_preresolved_1070_; lean_object* v___x_1071_; lean_object* v_pre_1072_; uint8_t v___x_1073_; 
v_val_1069_ = lean_ctor_get(v_stx_1058_, 2);
lean_inc(v_val_1069_);
v_preresolved_1070_ = lean_ctor_get(v_stx_1058_, 3);
v___x_1071_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1070_);
v_pre_1072_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1070_, v___x_1071_);
v___x_1073_ = l_List_isEmpty___redArg(v_pre_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v_val_1069_);
lean_dec_ref_known(v_stx_1058_, 4);
lean_dec_ref(v_k_1059_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_pre_1072_);
return v___x_1074_;
}
else
{
lean_object* v_toCold_1075_; lean_object* v_currRecDepth_1076_; lean_object* v_ref_1077_; uint16_t v_optionFlags_1078_; uint8_t v_suppressElabErrors_1079_; uint8_t v_isRecordingDeps_1080_; lean_object* v_ref_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_pre_1072_);
v_toCold_1075_ = lean_ctor_get(v___y_1066_, 0);
v_currRecDepth_1076_ = lean_ctor_get(v___y_1066_, 1);
v_ref_1077_ = lean_ctor_get(v___y_1066_, 2);
v_optionFlags_1078_ = lean_ctor_get_uint16(v___y_1066_, sizeof(void*)*3);
v_suppressElabErrors_1079_ = lean_ctor_get_uint8(v___y_1066_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1080_ = lean_ctor_get_uint8(v___y_1066_, sizeof(void*)*3 + 3);
v_ref_1081_ = l_Lean_replaceRef(v_stx_1058_, v_ref_1077_);
lean_dec_ref_known(v_stx_1058_, 4);
lean_inc(v_currRecDepth_1076_);
lean_inc_ref(v_toCold_1075_);
v___x_1082_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1082_, 0, v_toCold_1075_);
lean_ctor_set(v___x_1082_, 1, v_currRecDepth_1076_);
lean_ctor_set(v___x_1082_, 2, v_ref_1081_);
lean_ctor_set_uint16(v___x_1082_, sizeof(void*)*3, v_optionFlags_1078_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*3 + 2, v_suppressElabErrors_1079_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*3 + 3, v_isRecordingDeps_1080_);
lean_inc(v___y_1067_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
v___x_1083_ = lean_apply_10(v_k_1059_, v_val_1069_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___x_1082_, v___y_1067_, lean_box(0));
return v___x_1083_;
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_k_1059_);
v___x_1084_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1085_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1058_, v___x_1084_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v_stx_1058_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1086_, lean_object* v_k_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1086_, v_k_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1110_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1099_, v___x_1109_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1122_, size_t v_sz_1123_, size_t v_i_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_usize_dec_lt(v_i_1124_, v_sz_1123_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_b_1125_);
return v___x_1136_;
}
else
{
lean_object* v_a_1137_; lean_object* v_name_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_a_1137_ = lean_array_uget_borrowed(v_as_1122_, v_i_1124_);
v_name_1138_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_name_1138_);
v___x_1139_ = l_Lean_mkIdent(v_name_1138_);
lean_inc(v___x_1139_);
v___x_1140_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1139_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1139_, v_a_1141_, v_b_1125_, v___y_1132_);
lean_dec(v_a_1141_);
lean_dec(v___x_1139_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; size_t v___x_1144_; size_t v___x_1145_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1124_, v___x_1144_);
v_i_1124_ = v___x_1145_;
v_b_1125_ = v_a_1143_;
goto _start;
}
else
{
return v___x_1142_;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v___x_1139_);
lean_dec_ref(v_b_1125_);
v_a_1147_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1140_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1140_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1155_, lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
size_t v_sz_boxed_1168_; size_t v_i_boxed_1169_; lean_object* v_res_1170_; 
v_sz_boxed_1168_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1169_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1155_, v_sz_boxed_1168_, v_i_boxed_1169_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_as_1155_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1190_, lean_object* v_stx_1191_, uint8_t v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___f_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
if (v___x_1190_ == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_1206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v_tk_1208_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v___y_1282_; uint8_t v___y_1283_; lean_object* v___y_1284_; lean_object* v_stxForSuggestion_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; uint8_t v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; uint8_t v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; uint8_t v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; uint8_t v___y_1529_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_stxForExecution_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; uint8_t v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; uint8_t v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; uint8_t v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; uint8_t v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; uint8_t v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; uint8_t v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1811_; lean_object* v___y_1812_; uint8_t v___y_1813_; lean_object* v___y_1814_; uint8_t v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v_argsArray_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; uint8_t v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; uint8_t v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v_args_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___x_2006_; lean_object* v___y_2008_; uint8_t v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v_o_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v_bang_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v_tk_1208_ = l_Lean_Syntax_getArg(v_stx_1191_, v___x_1207_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2065_ = l_Lean_Syntax_getArg(v_stx_1191_, v___x_2006_);
v___x_2066_ = l_Lean_Syntax_isNone(v___x_2065_);
if (v___x_2066_ == 0)
{
uint8_t v___x_2067_; 
lean_inc(v___x_2065_);
v___x_2067_ = l_Lean_Syntax_matchesNull(v___x_2065_, v___x_2006_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
lean_dec(v___x_2065_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2068_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2068_;
}
else
{
lean_object* v_bang_2069_; lean_object* v___x_2070_; 
v_bang_2069_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_1207_);
lean_dec(v___x_2065_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_bang_2069_);
v_bang_2037_ = v___x_2070_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
v___y_2045_ = v___y_1204_;
goto v___jp_2036_;
}
}
else
{
lean_object* v___x_2071_; 
lean_dec(v___x_2065_);
v___x_2071_ = lean_box(0);
v_bang_2037_ = v___x_2071_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
v___y_2045_ = v___y_1204_;
goto v___jp_2036_;
}
v___jp_1209_:
{
lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_box(v___x_1192_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1224_, 0, v___y_1212_);
lean_closure_set(v___f_1224_, 1, v___x_1207_);
lean_closure_set(v___f_1224_, 2, v___x_1223_);
lean_closure_set(v___f_1224_, 3, v___y_1222_);
lean_closure_set(v___f_1224_, 4, v___y_1210_);
v___x_1225_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1211_, v___f_1224_, v___y_1220_, v___y_1216_, v___y_1215_, v___y_1218_, v___y_1213_, v___y_1221_, v___y_1214_, v___y_1219_);
lean_dec(v___y_1211_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_usedTheorems_1227_; lean_object* v_diag_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1270_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_usedTheorems_1227_ = lean_ctor_get(v_a_1226_, 0);
v_diag_1228_ = lean_ctor_get(v_a_1226_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1230_ = v_a_1226_;
v_isShared_1231_ = v_isSharedCheck_1270_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_diag_1228_);
lean_inc(v_usedTheorems_1227_);
lean_dec(v_a_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1270_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1217_, v_usedTheorems_1227_, v___y_1213_, v___y_1221_, v___y_1214_, v___y_1219_);
lean_dec_ref(v_usedTheorems_1227_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_ref_1234_ = lean_ctor_get(v___y_1214_, 2);
v___x_1235_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v_a_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1235_);
v___x_1237_ = v___x_1230_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_a_1233_);
v___x_1237_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
lean_ctor_set(v___x_1239_, 3, v___x_1238_);
lean_ctor_set(v___x_1239_, 4, v___x_1238_);
lean_ctor_set(v___x_1239_, 5, v___x_1238_);
lean_inc(v_ref_1234_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_ref_1234_);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1242_ = 4;
v___x_1243_ = l_Lean_MessageData_nil;
v___x_1244_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1208_, v___x_1239_, v___x_1240_, v___x_1241_, v___x_1238_, v___x_1242_, v___x_1243_, v___y_1214_, v___y_1219_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1252_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_diag_1228_);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_diag_1228_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_diag_1228_);
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1244_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1244_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_del_object(v___x_1230_);
lean_dec_ref(v_diag_1228_);
lean_dec(v_tk_1208_);
v_a_1262_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1232_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1232_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v___y_1217_);
lean_dec(v_tk_1208_);
v_a_1271_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1225_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1225_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
v___jp_1279_:
{
uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = 0;
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1296_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1284_, v___x_1294_, v___y_1283_, v___x_1294_, v___x_1295_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1284_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
if (lean_obj_tag(v___y_1282_) == 0)
{
lean_object* v_ctx_1298_; lean_object* v_simprocs_1299_; lean_object* v_dischargeWrapper_1300_; 
v_ctx_1298_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_ref(v_ctx_1298_);
v_simprocs_1299_ = lean_ctor_get(v_a_1297_, 1);
lean_inc_ref(v_simprocs_1299_);
v_dischargeWrapper_1300_ = lean_ctor_get(v_a_1297_, 2);
lean_inc(v_dischargeWrapper_1300_);
lean_dec(v_a_1297_);
v___y_1210_ = v_simprocs_1299_;
v___y_1211_ = v_dischargeWrapper_1300_;
v___y_1212_ = v___y_1280_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v___y_1292_;
v___y_1215_ = v___y_1288_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v_stxForSuggestion_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1293_;
v___y_1220_ = v___y_1286_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v_ctx_1298_;
goto v___jp_1209_;
}
else
{
lean_dec_ref_known(v___y_1282_, 1);
if (v___y_1281_ == 0)
{
lean_object* v_ctx_1301_; lean_object* v_simprocs_1302_; lean_object* v_dischargeWrapper_1303_; 
v_ctx_1301_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_ref(v_ctx_1301_);
v_simprocs_1302_ = lean_ctor_get(v_a_1297_, 1);
lean_inc_ref(v_simprocs_1302_);
v_dischargeWrapper_1303_ = lean_ctor_get(v_a_1297_, 2);
lean_inc(v_dischargeWrapper_1303_);
lean_dec(v_a_1297_);
v___y_1210_ = v_simprocs_1302_;
v___y_1211_ = v_dischargeWrapper_1303_;
v___y_1212_ = v___y_1280_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v___y_1292_;
v___y_1215_ = v___y_1288_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v_stxForSuggestion_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1293_;
v___y_1220_ = v___y_1286_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v_ctx_1301_;
goto v___jp_1209_;
}
else
{
lean_object* v_ctx_1304_; lean_object* v_simprocs_1305_; lean_object* v_dischargeWrapper_1306_; lean_object* v___x_1307_; 
v_ctx_1304_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_ref(v_ctx_1304_);
v_simprocs_1305_ = lean_ctor_get(v_a_1297_, 1);
lean_inc_ref(v_simprocs_1305_);
v_dischargeWrapper_1306_ = lean_ctor_get(v_a_1297_, 2);
lean_inc(v_dischargeWrapper_1306_);
lean_dec(v_a_1297_);
v___x_1307_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1304_);
v___y_1210_ = v_simprocs_1305_;
v___y_1211_ = v_dischargeWrapper_1306_;
v___y_1212_ = v___y_1280_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v___y_1292_;
v___y_1215_ = v___y_1288_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v_stxForSuggestion_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___y_1293_;
v___y_1220_ = v___y_1286_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v___x_1307_;
goto v___jp_1209_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_stxForSuggestion_1285_);
lean_dec(v___y_1282_);
lean_dec(v___y_1280_);
lean_dec(v_tk_1208_);
v_a_1308_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1296_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1296_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc_ref(v___y_1318_);
v___x_1340_ = l_Array_append___redArg(v___y_1318_, v___y_1339_);
lean_dec_ref(v___y_1339_);
lean_inc(v___y_1333_);
lean_inc(v___y_1324_);
v___x_1341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___y_1324_);
lean_ctor_set(v___x_1341_, 1, v___y_1333_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
v___x_1342_ = l_Lean_Syntax_node6(v___y_1324_, v___y_1322_, v___y_1329_, v___y_1335_, v___y_1330_, v___y_1321_, v___y_1319_, v___x_1341_);
v___y_1280_ = v___y_1317_;
v___y_1281_ = v___y_1331_;
v___y_1282_ = v___y_1323_;
v___y_1283_ = v___y_1327_;
v___y_1284_ = v___y_1336_;
v_stxForSuggestion_1285_ = v___x_1342_;
v___y_1286_ = v___y_1325_;
v___y_1287_ = v___y_1338_;
v___y_1288_ = v___y_1328_;
v___y_1289_ = v___y_1326_;
v___y_1290_ = v___y_1320_;
v___y_1291_ = v___y_1332_;
v___y_1292_ = v___y_1334_;
v___y_1293_ = v___y_1337_;
goto v___jp_1279_;
}
v___jp_1343_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_inc_ref_n(v___y_1345_, 2);
v___x_1367_ = l_Array_append___redArg(v___y_1345_, v___y_1366_);
lean_dec_ref(v___y_1366_);
lean_inc_n(v___y_1359_, 3);
lean_inc_n(v___y_1349_, 5);
v___x_1368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1368_, 0, v___y_1349_);
lean_ctor_set(v___x_1368_, 1, v___y_1359_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___y_1349_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1372_ = l_Lean_Syntax_SepArray_ofElems(v___x_1371_, v___y_1347_);
lean_dec_ref(v___y_1347_);
v___x_1373_ = l_Array_append___redArg(v___y_1345_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1374_, 0, v___y_1349_);
lean_ctor_set(v___x_1374_, 1, v___y_1359_);
lean_ctor_set(v___x_1374_, 2, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1349_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_node3(v___y_1349_, v___y_1359_, v___x_1370_, v___x_1374_, v___x_1376_);
if (lean_obj_tag(v___y_1364_) == 1)
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
v_val_1378_ = lean_ctor_get(v___y_1364_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v___y_1364_, 1);
v___x_1379_ = l_Array_mkArray1___redArg(v_val_1378_);
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___x_1377_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___x_1368_;
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1349_;
v___y_1325_ = v___y_1351_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1353_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1358_;
v___y_1333_ = v___y_1359_;
v___y_1334_ = v___y_1360_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1362_;
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___x_1379_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1380_; 
lean_dec(v___y_1364_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___x_1377_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___x_1368_;
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1349_;
v___y_1325_ = v___y_1351_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1353_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1358_;
v___y_1333_ = v___y_1359_;
v___y_1334_ = v___y_1360_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1362_;
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___x_1380_;
goto v___jp_1316_;
}
}
v___jp_1381_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_inc_ref(v___y_1383_);
v___x_1405_ = l_Array_append___redArg(v___y_1383_, v___y_1404_);
lean_dec_ref(v___y_1404_);
lean_inc(v___y_1397_);
lean_inc(v___y_1387_);
v___x_1406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___y_1387_);
lean_ctor_set(v___x_1406_, 1, v___y_1397_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
if (lean_obj_tag(v___y_1394_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_val_1407_ = lean_ctor_get(v___y_1394_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v___y_1394_, 1);
v___x_1408_ = l_Lean_SourceInfo_fromRef(v_val_1407_, v___x_1192_);
lean_dec(v_val_1407_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Array_mkArray1___redArg(v___x_1410_);
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1383_;
v___y_1346_ = v___y_1384_;
v___y_1347_ = v___y_1385_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___y_1389_;
v___y_1352_ = v___y_1390_;
v___y_1353_ = v___y_1391_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1406_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1398_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1403_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___x_1411_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1412_; 
lean_dec(v___y_1394_);
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1383_;
v___y_1346_ = v___y_1384_;
v___y_1347_ = v___y_1385_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___y_1389_;
v___y_1352_ = v___y_1390_;
v___y_1353_ = v___y_1391_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1406_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1398_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1403_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___x_1412_;
goto v___jp_1343_;
}
}
v___jp_1413_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc_ref(v___y_1420_);
v___x_1437_ = l_Array_append___redArg(v___y_1420_, v___y_1436_);
lean_dec_ref(v___y_1436_);
lean_inc(v___y_1425_);
lean_inc(v___y_1424_);
v___x_1438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1438_, 0, v___y_1424_);
lean_ctor_set(v___x_1438_, 1, v___y_1425_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
v___x_1439_ = l_Lean_Syntax_node6(v___y_1424_, v___y_1423_, v___y_1428_, v___y_1432_, v___y_1431_, v___y_1426_, v___y_1421_, v___x_1438_);
v___y_1280_ = v___y_1414_;
v___y_1281_ = v___y_1427_;
v___y_1282_ = v___y_1416_;
v___y_1283_ = v___y_1419_;
v___y_1284_ = v___y_1433_;
v_stxForSuggestion_1285_ = v___x_1439_;
v___y_1286_ = v___y_1417_;
v___y_1287_ = v___y_1435_;
v___y_1288_ = v___y_1422_;
v___y_1289_ = v___y_1418_;
v___y_1290_ = v___y_1415_;
v___y_1291_ = v___y_1429_;
v___y_1292_ = v___y_1430_;
v___y_1293_ = v___y_1434_;
goto v___jp_1279_;
}
v___jp_1440_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_inc_ref_n(v___y_1448_, 2);
v___x_1464_ = l_Array_append___redArg(v___y_1448_, v___y_1463_);
lean_dec_ref(v___y_1463_);
lean_inc_n(v___y_1452_, 3);
lean_inc_n(v___y_1451_, 5);
v___x_1465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1451_);
lean_ctor_set(v___x_1465_, 1, v___y_1452_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1451_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1469_ = l_Lean_Syntax_SepArray_ofElems(v___x_1468_, v___y_1443_);
lean_dec_ref(v___y_1443_);
v___x_1470_ = l_Array_append___redArg(v___y_1448_, v___x_1469_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1451_);
lean_ctor_set(v___x_1471_, 1, v___y_1452_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___y_1451_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_Syntax_node3(v___y_1451_, v___y_1452_, v___x_1467_, v___x_1471_, v___x_1473_);
if (lean_obj_tag(v___y_1461_) == 1)
{
lean_object* v_val_1475_; lean_object* v___x_1476_; 
v_val_1475_ = lean_ctor_get(v___y_1461_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___y_1461_, 1);
v___x_1476_ = l_Array_mkArray1___redArg(v_val_1475_);
v___y_1414_ = v___y_1441_;
v___y_1415_ = v___y_1442_;
v___y_1416_ = v___y_1444_;
v___y_1417_ = v___y_1445_;
v___y_1418_ = v___y_1446_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v___x_1474_;
v___y_1422_ = v___y_1449_;
v___y_1423_ = v___y_1450_;
v___y_1424_ = v___y_1451_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___x_1465_;
v___y_1427_ = v___y_1453_;
v___y_1428_ = v___y_1454_;
v___y_1429_ = v___y_1455_;
v___y_1430_ = v___y_1456_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1459_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___x_1476_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1477_; 
lean_dec(v___y_1461_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1414_ = v___y_1441_;
v___y_1415_ = v___y_1442_;
v___y_1416_ = v___y_1444_;
v___y_1417_ = v___y_1445_;
v___y_1418_ = v___y_1446_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v___x_1474_;
v___y_1422_ = v___y_1449_;
v___y_1423_ = v___y_1450_;
v___y_1424_ = v___y_1451_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___x_1465_;
v___y_1427_ = v___y_1453_;
v___y_1428_ = v___y_1454_;
v___y_1429_ = v___y_1455_;
v___y_1430_ = v___y_1456_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1459_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___x_1477_;
goto v___jp_1413_;
}
}
v___jp_1478_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc_ref(v___y_1486_);
v___x_1502_ = l_Array_append___redArg(v___y_1486_, v___y_1501_);
lean_dec_ref(v___y_1501_);
lean_inc(v___y_1491_);
lean_inc(v___y_1490_);
v___x_1503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1490_);
lean_ctor_set(v___x_1503_, 1, v___y_1491_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
if (lean_obj_tag(v___y_1488_) == 1)
{
lean_object* v_val_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_val_1504_ = lean_ctor_get(v___y_1488_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___y_1488_, 1);
v___x_1505_ = l_Lean_SourceInfo_fromRef(v_val_1504_, v___x_1192_);
lean_dec(v_val_1504_);
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Array_mkArray1___redArg(v___x_1507_);
v___y_1441_ = v___y_1479_;
v___y_1442_ = v___y_1480_;
v___y_1443_ = v___y_1481_;
v___y_1444_ = v___y_1482_;
v___y_1445_ = v___y_1483_;
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1486_;
v___y_1449_ = v___y_1487_;
v___y_1450_ = v___y_1489_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___x_1503_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1497_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1499_;
v___y_1463_ = v___x_1508_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1509_; 
lean_dec(v___y_1488_);
v___x_1509_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1441_ = v___y_1479_;
v___y_1442_ = v___y_1480_;
v___y_1443_ = v___y_1481_;
v___y_1444_ = v___y_1482_;
v___y_1445_ = v___y_1483_;
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1486_;
v___y_1449_ = v___y_1487_;
v___y_1450_ = v___y_1489_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___x_1503_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1497_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1499_;
v___y_1463_ = v___x_1509_;
goto v___jp_1440_;
}
}
v___jp_1510_:
{
lean_object* v_ref_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_ref_1530_ = lean_ctor_get(v___y_1523_, 2);
v___x_1531_ = l_Lean_SourceInfo_fromRef(v_ref_1530_, v___y_1529_);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1533_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_1532_);
v___x_1534_ = l_Lean_SourceInfo_fromRef(v_tk_1208_, v___x_1192_);
v___x_1535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1532_);
v___x_1536_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1537_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1519_) == 1)
{
lean_object* v_val_1538_; lean_object* v___x_1539_; 
v_val_1538_ = lean_ctor_get(v___y_1519_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___y_1519_, 1);
v___x_1539_ = l_Array_mkArray1___redArg(v_val_1538_);
v___y_1479_ = v___y_1511_;
v___y_1480_ = v___y_1512_;
v___y_1481_ = v___y_1513_;
v___y_1482_ = v___y_1514_;
v___y_1483_ = v___y_1515_;
v___y_1484_ = v___y_1516_;
v___y_1485_ = v___y_1517_;
v___y_1486_ = v___x_1537_;
v___y_1487_ = v___y_1518_;
v___y_1488_ = v___y_1520_;
v___y_1489_ = v___x_1533_;
v___y_1490_ = v___x_1531_;
v___y_1491_ = v___x_1536_;
v___y_1492_ = v___y_1521_;
v___y_1493_ = v___x_1535_;
v___y_1494_ = v___y_1522_;
v___y_1495_ = v___y_1523_;
v___y_1496_ = v___y_1524_;
v___y_1497_ = v___y_1526_;
v___y_1498_ = v___y_1525_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1527_;
v___y_1501_ = v___x_1539_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v___y_1519_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1479_ = v___y_1511_;
v___y_1480_ = v___y_1512_;
v___y_1481_ = v___y_1513_;
v___y_1482_ = v___y_1514_;
v___y_1483_ = v___y_1515_;
v___y_1484_ = v___y_1516_;
v___y_1485_ = v___y_1517_;
v___y_1486_ = v___x_1537_;
v___y_1487_ = v___y_1518_;
v___y_1488_ = v___y_1520_;
v___y_1489_ = v___x_1533_;
v___y_1490_ = v___x_1531_;
v___y_1491_ = v___x_1536_;
v___y_1492_ = v___y_1521_;
v___y_1493_ = v___x_1535_;
v___y_1494_ = v___y_1522_;
v___y_1495_ = v___y_1523_;
v___y_1496_ = v___y_1524_;
v___y_1497_ = v___y_1526_;
v___y_1498_ = v___y_1525_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1527_;
v___y_1501_ = v___x_1540_;
goto v___jp_1478_;
}
}
v___jp_1541_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1547_);
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v___x_1562_ = 0;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1556_;
v___y_1513_ = v___y_1544_;
v___y_1514_ = v___y_1546_;
v___y_1515_ = v___y_1552_;
v___y_1516_ = v___y_1555_;
v___y_1517_ = v___y_1548_;
v___y_1518_ = v___y_1554_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1543_;
v___y_1521_ = v___y_1545_;
v___y_1522_ = v___y_1557_;
v___y_1523_ = v___y_1558_;
v___y_1524_ = v_a_1561_;
v___y_1525_ = v___y_1559_;
v___y_1526_ = v_stxForExecution_1551_;
v___y_1527_ = v___y_1549_;
v___y_1528_ = v___y_1553_;
v___y_1529_ = v___x_1562_;
goto v___jp_1510_;
}
else
{
if (v___y_1545_ == 0)
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1560_);
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1556_;
v___y_1513_ = v___y_1544_;
v___y_1514_ = v___y_1546_;
v___y_1515_ = v___y_1552_;
v___y_1516_ = v___y_1555_;
v___y_1517_ = v___y_1548_;
v___y_1518_ = v___y_1554_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1543_;
v___y_1521_ = v___y_1545_;
v___y_1522_ = v___y_1557_;
v___y_1523_ = v___y_1558_;
v___y_1524_ = v_a_1563_;
v___y_1525_ = v___y_1559_;
v___y_1526_ = v_stxForExecution_1551_;
v___y_1527_ = v___y_1549_;
v___y_1528_ = v___y_1553_;
v___y_1529_ = v___y_1545_;
goto v___jp_1510_;
}
else
{
lean_object* v_a_1564_; lean_object* v_ref_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1560_);
v_ref_1565_ = lean_ctor_get(v___y_1558_, 2);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_SourceInfo_fromRef(v_ref_1565_, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1569_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_1568_);
v___x_1570_ = l_Lean_SourceInfo_fromRef(v_tk_1208_, v___x_1192_);
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1574_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1550_) == 1)
{
lean_object* v_val_1575_; lean_object* v___x_1576_; 
v_val_1575_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___y_1550_, 1);
v___x_1576_ = l_Array_mkArray1___redArg(v_val_1575_);
v___y_1382_ = v___y_1542_;
v___y_1383_ = v___x_1574_;
v___y_1384_ = v___y_1556_;
v___y_1385_ = v___y_1544_;
v___y_1386_ = v___x_1569_;
v___y_1387_ = v___x_1567_;
v___y_1388_ = v___y_1546_;
v___y_1389_ = v___y_1552_;
v___y_1390_ = v___y_1555_;
v___y_1391_ = v___y_1548_;
v___y_1392_ = v___y_1554_;
v___y_1393_ = v___x_1572_;
v___y_1394_ = v___y_1543_;
v___y_1395_ = v___y_1545_;
v___y_1396_ = v___y_1557_;
v___y_1397_ = v___x_1573_;
v___y_1398_ = v___y_1558_;
v___y_1399_ = v_a_1564_;
v___y_1400_ = v_stxForExecution_1551_;
v___y_1401_ = v___y_1559_;
v___y_1402_ = v___y_1553_;
v___y_1403_ = v___y_1549_;
v___y_1404_ = v___x_1576_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1577_; 
lean_dec(v___y_1550_);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1382_ = v___y_1542_;
v___y_1383_ = v___x_1574_;
v___y_1384_ = v___y_1556_;
v___y_1385_ = v___y_1544_;
v___y_1386_ = v___x_1569_;
v___y_1387_ = v___x_1567_;
v___y_1388_ = v___y_1546_;
v___y_1389_ = v___y_1552_;
v___y_1390_ = v___y_1555_;
v___y_1391_ = v___y_1548_;
v___y_1392_ = v___y_1554_;
v___y_1393_ = v___x_1572_;
v___y_1394_ = v___y_1543_;
v___y_1395_ = v___y_1545_;
v___y_1396_ = v___y_1557_;
v___y_1397_ = v___x_1573_;
v___y_1398_ = v___y_1558_;
v___y_1399_ = v_a_1564_;
v___y_1400_ = v_stxForExecution_1551_;
v___y_1401_ = v___y_1559_;
v___y_1402_ = v___y_1553_;
v___y_1403_ = v___y_1549_;
v___y_1404_ = v___x_1577_;
goto v___jp_1381_;
}
}
}
}
v___jp_1578_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_inc_ref(v___y_1589_);
v___x_1605_ = l_Array_append___redArg(v___y_1589_, v___y_1604_);
lean_dec_ref(v___y_1604_);
lean_inc(v___y_1600_);
lean_inc(v___y_1587_);
v___x_1606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1587_);
lean_ctor_set(v___x_1606_, 1, v___y_1600_);
lean_ctor_set(v___x_1606_, 2, v___x_1605_);
lean_inc(v___y_1585_);
v___x_1607_ = l_Lean_Syntax_node6(v___y_1587_, v___y_1583_, v___y_1592_, v___y_1585_, v___y_1586_, v___y_1594_, v___y_1602_, v___x_1606_);
v___y_1542_ = v___y_1579_;
v___y_1543_ = v___y_1597_;
v___y_1544_ = v___y_1582_;
v___y_1545_ = v___y_1598_;
v___y_1546_ = v___y_1590_;
v___y_1547_ = v___y_1585_;
v___y_1548_ = v___y_1591_;
v___y_1549_ = v___y_1603_;
v___y_1550_ = v___y_1593_;
v_stxForExecution_1551_ = v___x_1607_;
v___y_1552_ = v___y_1596_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1580_;
v___y_1555_ = v___y_1588_;
v___y_1556_ = v___y_1595_;
v___y_1557_ = v___y_1599_;
v___y_1558_ = v___y_1601_;
v___y_1559_ = v___y_1584_;
goto v___jp_1541_;
}
v___jp_1608_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_inc_ref_n(v___y_1615_, 2);
v___x_1633_ = l_Array_append___redArg(v___y_1615_, v___y_1632_);
lean_dec_ref(v___y_1632_);
lean_inc_n(v___y_1627_, 3);
lean_inc_n(v___y_1629_, 5);
v___x_1634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1629_);
lean_ctor_set(v___x_1634_, 1, v___y_1627_);
lean_ctor_set(v___x_1634_, 2, v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___y_1629_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1638_ = l_Lean_Syntax_SepArray_ofElems(v___x_1637_, v___y_1612_);
v___x_1639_ = l_Array_append___redArg(v___y_1615_, v___x_1638_);
lean_dec_ref(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1629_);
lean_ctor_set(v___x_1640_, 1, v___y_1627_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___y_1629_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_Syntax_node3(v___y_1629_, v___y_1627_, v___x_1636_, v___x_1640_, v___x_1642_);
if (lean_obj_tag(v___y_1631_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1645_; 
v_val_1644_ = lean_ctor_get(v___y_1631_, 0);
lean_inc(v_val_1644_);
v___x_1645_ = l_Array_mkArray1___redArg(v_val_1644_);
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___y_1610_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1612_;
v___y_1583_ = v___y_1614_;
v___y_1584_ = v___y_1618_;
v___y_1585_ = v___y_1628_;
v___y_1586_ = v___y_1630_;
v___y_1587_ = v___y_1629_;
v___y_1588_ = v___y_1613_;
v___y_1589_ = v___y_1615_;
v___y_1590_ = v___y_1616_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1620_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v___x_1634_;
v___y_1595_ = v___y_1621_;
v___y_1596_ = v___y_1623_;
v___y_1597_ = v___y_1622_;
v___y_1598_ = v___y_1624_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1627_;
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___x_1643_;
v___y_1603_ = v___y_1631_;
v___y_1604_ = v___x_1645_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___y_1610_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1612_;
v___y_1583_ = v___y_1614_;
v___y_1584_ = v___y_1618_;
v___y_1585_ = v___y_1628_;
v___y_1586_ = v___y_1630_;
v___y_1587_ = v___y_1629_;
v___y_1588_ = v___y_1613_;
v___y_1589_ = v___y_1615_;
v___y_1590_ = v___y_1616_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1620_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v___x_1634_;
v___y_1595_ = v___y_1621_;
v___y_1596_ = v___y_1623_;
v___y_1597_ = v___y_1622_;
v___y_1598_ = v___y_1624_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1627_;
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___x_1643_;
v___y_1603_ = v___y_1631_;
v___y_1604_ = v___x_1646_;
goto v___jp_1578_;
}
}
v___jp_1647_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref(v___y_1654_);
v___x_1671_ = l_Array_append___redArg(v___y_1654_, v___y_1670_);
lean_dec_ref(v___y_1670_);
lean_inc(v___y_1667_);
lean_inc(v___y_1668_);
v___x_1672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1668_);
lean_ctor_set(v___x_1672_, 1, v___y_1667_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
if (lean_obj_tag(v___y_1662_) == 1)
{
lean_object* v_val_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_val_1673_ = lean_ctor_get(v___y_1662_, 0);
v___x_1674_ = l_Lean_SourceInfo_fromRef(v_val_1673_, v___x_1192_);
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Array_mkArray1___redArg(v___x_1676_);
v___y_1609_ = v___y_1648_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v___y_1612_ = v___y_1651_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1654_;
v___y_1616_ = v___y_1655_;
v___y_1617_ = v___y_1656_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1658_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1666_;
v___y_1627_ = v___y_1667_;
v___y_1628_ = v___y_1665_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___x_1672_;
v___y_1631_ = v___y_1669_;
v___y_1632_ = v___x_1677_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1609_ = v___y_1648_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v___y_1612_ = v___y_1651_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1654_;
v___y_1616_ = v___y_1655_;
v___y_1617_ = v___y_1656_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1658_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1666_;
v___y_1627_ = v___y_1667_;
v___y_1628_ = v___y_1665_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___x_1672_;
v___y_1631_ = v___y_1669_;
v___y_1632_ = v___x_1678_;
goto v___jp_1608_;
}
}
v___jp_1679_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_inc_ref(v___y_1681_);
v___x_1706_ = l_Array_append___redArg(v___y_1681_, v___y_1705_);
lean_dec_ref(v___y_1705_);
lean_inc(v___y_1693_);
lean_inc(v___y_1684_);
v___x_1707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1684_);
lean_ctor_set(v___x_1707_, 1, v___y_1693_);
lean_ctor_set(v___x_1707_, 2, v___x_1706_);
lean_inc(v___y_1687_);
v___x_1708_ = l_Lean_Syntax_node6(v___y_1684_, v___y_1702_, v___y_1701_, v___y_1687_, v___y_1690_, v___y_1703_, v___y_1696_, v___x_1707_);
v___y_1542_ = v___y_1680_;
v___y_1543_ = v___y_1697_;
v___y_1544_ = v___y_1685_;
v___y_1545_ = v___y_1698_;
v___y_1546_ = v___y_1689_;
v___y_1547_ = v___y_1687_;
v___y_1548_ = v___y_1691_;
v___y_1549_ = v___y_1704_;
v___y_1550_ = v___y_1692_;
v_stxForExecution_1551_ = v___x_1708_;
v___y_1552_ = v___y_1695_;
v___y_1553_ = v___y_1683_;
v___y_1554_ = v___y_1682_;
v___y_1555_ = v___y_1688_;
v___y_1556_ = v___y_1694_;
v___y_1557_ = v___y_1699_;
v___y_1558_ = v___y_1700_;
v___y_1559_ = v___y_1686_;
goto v___jp_1541_;
}
v___jp_1709_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_inc_ref_n(v___y_1711_, 2);
v___x_1734_ = l_Array_append___redArg(v___y_1711_, v___y_1733_);
lean_dec_ref(v___y_1733_);
lean_inc_n(v___y_1723_, 3);
lean_inc_n(v___y_1714_, 5);
v___x_1735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1735_, 0, v___y_1714_);
lean_ctor_set(v___x_1735_, 1, v___y_1723_);
lean_ctor_set(v___x_1735_, 2, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1714_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1739_ = l_Lean_Syntax_SepArray_ofElems(v___x_1738_, v___y_1715_);
v___x_1740_ = l_Array_append___redArg(v___y_1711_, v___x_1739_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1741_, 0, v___y_1714_);
lean_ctor_set(v___x_1741_, 1, v___y_1723_);
lean_ctor_set(v___x_1741_, 2, v___x_1740_);
v___x_1742_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___y_1714_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_Syntax_node3(v___y_1714_, v___y_1723_, v___x_1737_, v___x_1741_, v___x_1743_);
if (lean_obj_tag(v___y_1732_) == 1)
{
lean_object* v_val_1745_; lean_object* v___x_1746_; 
v_val_1745_ = lean_ctor_get(v___y_1732_, 0);
lean_inc(v_val_1745_);
v___x_1746_ = l_Array_mkArray1___redArg(v_val_1745_);
v___y_1680_ = v___y_1710_;
v___y_1681_ = v___y_1711_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1720_;
v___y_1687_ = v___y_1729_;
v___y_1688_ = v___y_1716_;
v___y_1689_ = v___y_1717_;
v___y_1690_ = v___y_1718_;
v___y_1691_ = v___y_1719_;
v___y_1692_ = v___y_1721_;
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1722_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___x_1744_;
v___y_1697_ = v___y_1724_;
v___y_1698_ = v___y_1726_;
v___y_1699_ = v___y_1727_;
v___y_1700_ = v___y_1728_;
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1730_;
v___y_1703_ = v___x_1735_;
v___y_1704_ = v___y_1732_;
v___y_1705_ = v___x_1746_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1680_ = v___y_1710_;
v___y_1681_ = v___y_1711_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1720_;
v___y_1687_ = v___y_1729_;
v___y_1688_ = v___y_1716_;
v___y_1689_ = v___y_1717_;
v___y_1690_ = v___y_1718_;
v___y_1691_ = v___y_1719_;
v___y_1692_ = v___y_1721_;
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1722_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___x_1744_;
v___y_1697_ = v___y_1724_;
v___y_1698_ = v___y_1726_;
v___y_1699_ = v___y_1727_;
v___y_1700_ = v___y_1728_;
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1730_;
v___y_1703_ = v___x_1735_;
v___y_1704_ = v___y_1732_;
v___y_1705_ = v___x_1747_;
goto v___jp_1679_;
}
}
v___jp_1748_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_inc_ref(v___y_1750_);
v___x_1772_ = l_Array_append___redArg(v___y_1750_, v___y_1771_);
lean_dec_ref(v___y_1771_);
lean_inc(v___y_1760_);
lean_inc(v___y_1753_);
v___x_1773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1773_, 0, v___y_1753_);
lean_ctor_set(v___x_1773_, 1, v___y_1760_);
lean_ctor_set(v___x_1773_, 2, v___x_1772_);
if (lean_obj_tag(v___y_1763_) == 1)
{
lean_object* v_val_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_val_1774_ = lean_ctor_get(v___y_1763_, 0);
v___x_1775_ = l_Lean_SourceInfo_fromRef(v_val_1774_, v___x_1192_);
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Array_mkArray1___redArg(v___x_1777_);
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___y_1751_;
v___y_1713_ = v___y_1752_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___y_1756_;
v___y_1718_ = v___x_1773_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1758_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1762_;
v___y_1726_ = v___y_1764_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1767_;
v___y_1729_ = v___y_1766_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___x_1778_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___y_1751_;
v___y_1713_ = v___y_1752_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___y_1756_;
v___y_1718_ = v___x_1773_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1758_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1762_;
v___y_1726_ = v___y_1764_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1767_;
v___y_1729_ = v___y_1766_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___x_1779_;
goto v___jp_1709_;
}
}
v___jp_1780_:
{
lean_object* v_ref_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_ref_1799_ = lean_ctor_get(v___y_1796_, 2);
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_ref_1799_, v___y_1798_);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
v___x_1802_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_1801_);
v___x_1803_ = l_Lean_SourceInfo_fromRef(v_tk_1208_, v___x_1192_);
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1801_);
v___x_1805_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1806_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1789_) == 1)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; 
v_val_1807_ = lean_ctor_get(v___y_1789_, 0);
lean_inc(v_val_1807_);
v___x_1808_ = l_Array_mkArray1___redArg(v_val_1807_);
v___y_1749_ = v___y_1781_;
v___y_1750_ = v___x_1806_;
v___y_1751_ = v___y_1782_;
v___y_1752_ = v___y_1783_;
v___y_1753_ = v___x_1800_;
v___y_1754_ = v___y_1784_;
v___y_1755_ = v___y_1785_;
v___y_1756_ = v___y_1786_;
v___y_1757_ = v___y_1787_;
v___y_1758_ = v___y_1788_;
v___y_1759_ = v___y_1789_;
v___y_1760_ = v___x_1805_;
v___y_1761_ = v___y_1790_;
v___y_1762_ = v___y_1791_;
v___y_1763_ = v___y_1792_;
v___y_1764_ = v___y_1793_;
v___y_1765_ = v___y_1794_;
v___y_1766_ = v___y_1795_;
v___y_1767_ = v___y_1796_;
v___y_1768_ = v___x_1804_;
v___y_1769_ = v___x_1802_;
v___y_1770_ = v___y_1797_;
v___y_1771_ = v___x_1808_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1749_ = v___y_1781_;
v___y_1750_ = v___x_1806_;
v___y_1751_ = v___y_1782_;
v___y_1752_ = v___y_1783_;
v___y_1753_ = v___x_1800_;
v___y_1754_ = v___y_1784_;
v___y_1755_ = v___y_1785_;
v___y_1756_ = v___y_1786_;
v___y_1757_ = v___y_1787_;
v___y_1758_ = v___y_1788_;
v___y_1759_ = v___y_1789_;
v___y_1760_ = v___x_1805_;
v___y_1761_ = v___y_1790_;
v___y_1762_ = v___y_1791_;
v___y_1763_ = v___y_1792_;
v___y_1764_ = v___y_1793_;
v___y_1765_ = v___y_1794_;
v___y_1766_ = v___y_1795_;
v___y_1767_ = v___y_1796_;
v___y_1768_ = v___x_1804_;
v___y_1769_ = v___x_1802_;
v___y_1770_ = v___y_1797_;
v___y_1771_ = v___x_1809_;
goto v___jp_1748_;
}
}
v___jp_1810_:
{
if (lean_obj_tag(v___y_1814_) == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = 0;
v___y_1781_ = v___y_1811_;
v___y_1782_ = v___y_1822_;
v___y_1783_ = v___y_1821_;
v___y_1784_ = v_argsArray_1819_;
v___y_1785_ = v___y_1823_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1827_;
v___y_1789_ = v___y_1817_;
v___y_1790_ = v___y_1824_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1812_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1825_;
v___y_1795_ = v___y_1816_;
v___y_1796_ = v___y_1826_;
v___y_1797_ = v___y_1818_;
v___y_1798_ = v___x_1828_;
goto v___jp_1780_;
}
else
{
if (v___y_1813_ == 0)
{
v___y_1781_ = v___y_1811_;
v___y_1782_ = v___y_1822_;
v___y_1783_ = v___y_1821_;
v___y_1784_ = v_argsArray_1819_;
v___y_1785_ = v___y_1823_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1827_;
v___y_1789_ = v___y_1817_;
v___y_1790_ = v___y_1824_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1812_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1825_;
v___y_1795_ = v___y_1816_;
v___y_1796_ = v___y_1826_;
v___y_1797_ = v___y_1818_;
v___y_1798_ = v___y_1813_;
goto v___jp_1780_;
}
else
{
lean_object* v_ref_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_ref_1829_ = lean_ctor_get(v___y_1826_, 2);
v___x_1830_ = 0;
v___x_1831_ = l_Lean_SourceInfo_fromRef(v_ref_1829_, v___x_1830_);
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
v___x_1833_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_1832_);
v___x_1834_ = l_Lean_SourceInfo_fromRef(v_tk_1208_, v___x_1192_);
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1838_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1817_) == 1)
{
lean_object* v_val_1839_; lean_object* v___x_1840_; 
v_val_1839_ = lean_ctor_get(v___y_1817_, 0);
lean_inc(v_val_1839_);
v___x_1840_ = l_Array_mkArray1___redArg(v_val_1839_);
v___y_1648_ = v___y_1811_;
v___y_1649_ = v___y_1822_;
v___y_1650_ = v___y_1821_;
v___y_1651_ = v_argsArray_1819_;
v___y_1652_ = v___y_1823_;
v___y_1653_ = v___x_1833_;
v___y_1654_ = v___x_1838_;
v___y_1655_ = v___y_1814_;
v___y_1656_ = v___y_1815_;
v___y_1657_ = v___y_1827_;
v___y_1658_ = v___y_1817_;
v___y_1659_ = v___x_1836_;
v___y_1660_ = v___y_1824_;
v___y_1661_ = v___y_1820_;
v___y_1662_ = v___y_1812_;
v___y_1663_ = v___y_1813_;
v___y_1664_ = v___y_1825_;
v___y_1665_ = v___y_1816_;
v___y_1666_ = v___y_1826_;
v___y_1667_ = v___x_1837_;
v___y_1668_ = v___x_1831_;
v___y_1669_ = v___y_1818_;
v___y_1670_ = v___x_1840_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1841_; 
v___x_1841_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1648_ = v___y_1811_;
v___y_1649_ = v___y_1822_;
v___y_1650_ = v___y_1821_;
v___y_1651_ = v_argsArray_1819_;
v___y_1652_ = v___y_1823_;
v___y_1653_ = v___x_1833_;
v___y_1654_ = v___x_1838_;
v___y_1655_ = v___y_1814_;
v___y_1656_ = v___y_1815_;
v___y_1657_ = v___y_1827_;
v___y_1658_ = v___y_1817_;
v___y_1659_ = v___x_1836_;
v___y_1660_ = v___y_1824_;
v___y_1661_ = v___y_1820_;
v___y_1662_ = v___y_1812_;
v___y_1663_ = v___y_1813_;
v___y_1664_ = v___y_1825_;
v___y_1665_ = v___y_1816_;
v___y_1666_ = v___y_1826_;
v___y_1667_ = v___x_1837_;
v___y_1668_ = v___x_1831_;
v___y_1669_ = v___y_1818_;
v___y_1670_ = v___x_1841_;
goto v___jp_1647_;
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1844_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1857_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = l_Lean_LibrarySuggestions_select(v_a_1862_, v___y_1860_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1857_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; size_t v_sz_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v_sz_1865_ = lean_array_size(v_a_1864_);
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1864_, v_sz_1865_, v___x_1866_, v___y_1849_, v___y_1858_, v___y_1844_, v___y_1852_, v___y_1848_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1857_);
lean_dec(v_a_1864_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___y_1811_ = v___y_1843_;
v___y_1812_ = v___y_1850_;
v___y_1813_ = v___y_1855_;
v___y_1814_ = v___y_1845_;
v___y_1815_ = v___y_1846_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___y_1847_;
v___y_1818_ = v___y_1859_;
v_argsArray_1819_ = v_a_1868_;
v___y_1820_ = v___y_1858_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1852_;
v___y_1823_ = v___y_1848_;
v___y_1824_ = v___y_1851_;
v___y_1825_ = v___y_1853_;
v___y_1826_ = v___y_1854_;
v___y_1827_ = v___y_1857_;
goto v___jp_1810_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v___y_1859_);
lean_dec(v___y_1856_);
lean_dec(v___y_1850_);
lean_dec(v___y_1847_);
lean_dec(v___y_1845_);
lean_dec(v___y_1843_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v_a_1869_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v___y_1859_);
lean_dec(v___y_1856_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1847_);
lean_dec(v___y_1845_);
lean_dec(v___y_1843_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v_a_1877_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1863_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1863_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1856_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1847_);
lean_dec(v___y_1845_);
lean_dec(v___y_1843_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v_a_1885_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1861_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1861_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
v___jp_1893_:
{
lean_object* v_config_1912_; uint8_t v_suggestions_1913_; 
v_config_1912_ = lean_ctor_get(v___y_1896_, 0);
lean_inc_ref(v_config_1912_);
lean_dec_ref(v___y_1896_);
v_suggestions_1913_ = lean_ctor_get_uint8(v_config_1912_, sizeof(void*)*3 + 26);
if (v_suggestions_1913_ == 0)
{
lean_dec_ref(v_config_1912_);
lean_dec_ref(v___f_1196_);
v___y_1811_ = v___y_1894_;
v___y_1812_ = v___y_1901_;
v___y_1813_ = v___y_1906_;
v___y_1814_ = v___y_1897_;
v___y_1815_ = v___y_1898_;
v___y_1816_ = v___y_1907_;
v___y_1817_ = v___y_1899_;
v___y_1818_ = v___y_1910_;
v_argsArray_1819_ = v___y_1911_;
v___y_1820_ = v___y_1908_;
v___y_1821_ = v___y_1895_;
v___y_1822_ = v___y_1903_;
v___y_1823_ = v___y_1900_;
v___y_1824_ = v___y_1902_;
v___y_1825_ = v___y_1904_;
v___y_1826_ = v___y_1905_;
v___y_1827_ = v___y_1909_;
goto v___jp_1810_;
}
else
{
lean_object* v_maxSuggestions_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_maxSuggestions_1914_ = lean_ctor_get(v_config_1912_, 2);
lean_inc(v_maxSuggestions_1914_);
lean_dec_ref(v_config_1912_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1916_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1914_) == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_unsigned_to_nat(100u);
v___x_1918_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1915_);
lean_ctor_set(v___x_1918_, 2, v___f_1196_);
lean_ctor_set(v___x_1918_, 3, v___x_1916_);
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1897_;
v___y_1846_ = v___y_1898_;
v___y_1847_ = v___y_1899_;
v___y_1848_ = v___y_1900_;
v___y_1849_ = v___y_1911_;
v___y_1850_ = v___y_1901_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1904_;
v___y_1854_ = v___y_1905_;
v___y_1855_ = v___y_1906_;
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1909_;
v___y_1858_ = v___y_1908_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___x_1918_;
goto v___jp_1842_;
}
else
{
lean_object* v_val_1919_; lean_object* v___x_1920_; 
v_val_1919_ = lean_ctor_get(v_maxSuggestions_1914_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_maxSuggestions_1914_, 1);
v___x_1920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1920_, 0, v_val_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1915_);
lean_ctor_set(v___x_1920_, 2, v___f_1196_);
lean_ctor_set(v___x_1920_, 3, v___x_1916_);
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1897_;
v___y_1846_ = v___y_1898_;
v___y_1847_ = v___y_1899_;
v___y_1848_ = v___y_1900_;
v___y_1849_ = v___y_1911_;
v___y_1850_ = v___y_1901_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1904_;
v___y_1854_ = v___y_1905_;
v___y_1855_ = v___y_1906_;
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1909_;
v___y_1858_ = v___y_1908_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___x_1920_;
goto v___jp_1842_;
}
}
}
v___jp_1921_:
{
uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = 0;
lean_inc(v___y_1928_);
v___x_1938_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1928_, v___x_1937_, v___y_1933_, v___y_1932_, v___y_1934_);
if (lean_obj_tag(v___x_1938_) == 0)
{
if (lean_obj_tag(v___y_1925_) == 1)
{
lean_object* v_a_1939_; lean_object* v_val_1940_; lean_object* v___x_1941_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_val_1940_ = lean_ctor_get(v___y_1925_, 0);
lean_inc(v_val_1940_);
lean_dec_ref_known(v___y_1925_, 1);
v___x_1941_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1940_);
lean_dec(v_val_1940_);
lean_inc(v___y_1929_);
v___y_1894_ = v___y_1929_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v_a_1939_;
v___y_1897_ = v___y_1935_;
v___y_1898_ = v___x_1937_;
v___y_1899_ = v___y_1936_;
v___y_1900_ = v___y_1927_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___y_1923_;
v___y_1903_ = v___y_1931_;
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v___y_1926_;
v___y_1907_ = v___y_1928_;
v___y_1908_ = v___y_1933_;
v___y_1909_ = v___y_1934_;
v___y_1910_ = v___y_1929_;
v___y_1911_ = v___x_1941_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1943_; 
lean_dec(v___y_1925_);
v_a_1942_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1929_);
v___y_1894_ = v___y_1929_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v_a_1942_;
v___y_1897_ = v___y_1935_;
v___y_1898_ = v___x_1937_;
v___y_1899_ = v___y_1936_;
v___y_1900_ = v___y_1927_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___y_1923_;
v___y_1903_ = v___y_1931_;
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v___y_1926_;
v___y_1907_ = v___y_1928_;
v___y_1908_ = v___y_1933_;
v___y_1909_ = v___y_1934_;
v___y_1910_ = v___y_1929_;
v___y_1911_ = v___x_1943_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1925_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v_a_1944_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1938_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1938_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
v___jp_1952_:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Syntax_getOptional_x3f(v___y_1955_);
lean_dec(v___y_1955_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_box(0);
v___y_1922_ = v___y_1953_;
v___y_1923_ = v___y_1959_;
v___y_1924_ = v___y_1961_;
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___y_1962_;
v___y_1927_ = v___y_1956_;
v___y_1928_ = v___y_1964_;
v___y_1929_ = v___y_1967_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1960_;
v___y_1932_ = v___y_1963_;
v___y_1933_ = v___y_1966_;
v___y_1934_ = v___y_1965_;
v___y_1935_ = v___y_1954_;
v___y_1936_ = v___x_1969_;
goto v___jp_1921_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_val_1970_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1968_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v___x_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_val_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
v___y_1922_ = v___y_1953_;
v___y_1923_ = v___y_1959_;
v___y_1924_ = v___y_1961_;
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___y_1962_;
v___y_1927_ = v___y_1956_;
v___y_1928_ = v___y_1964_;
v___y_1929_ = v___y_1967_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1960_;
v___y_1932_ = v___y_1963_;
v___y_1933_ = v___y_1966_;
v___y_1934_ = v___y_1965_;
v___y_1935_ = v___y_1954_;
v___y_1936_ = v___x_1975_;
goto v___jp_1921_;
}
}
}
}
v___jp_1978_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_unsigned_to_nat(4u);
v___x_1995_ = l_Lean_Syntax_getArg(v___y_1979_, v___x_1994_);
lean_dec(v___y_1979_);
v___x_1996_ = l_Lean_Syntax_getOptional_x3f(v___x_1995_);
lean_dec(v___x_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_box(0);
v___y_1953_ = v___y_1987_;
v___y_1954_ = v___y_1982_;
v___y_1955_ = v___y_1984_;
v___y_1956_ = v___y_1989_;
v___y_1957_ = v_args_1985_;
v___y_1958_ = v___y_1980_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1988_;
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1981_;
v___y_1963_ = v___y_1992_;
v___y_1964_ = v___y_1983_;
v___y_1965_ = v___y_1993_;
v___y_1966_ = v___y_1986_;
v___y_1967_ = v___x_1997_;
goto v___jp_1952_;
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_val_1998_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1996_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_val_1998_);
lean_dec(v___x_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_val_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v___y_1953_ = v___y_1987_;
v___y_1954_ = v___y_1982_;
v___y_1955_ = v___y_1984_;
v___y_1956_ = v___y_1989_;
v___y_1957_ = v_args_1985_;
v___y_1958_ = v___y_1980_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1988_;
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1981_;
v___y_1963_ = v___y_1992_;
v___y_1964_ = v___y_1983_;
v___y_1965_ = v___y_1993_;
v___y_1966_ = v___y_1986_;
v___y_1967_ = v___x_2003_;
goto v___jp_1952_;
}
}
}
}
v___jp_2007_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(3u);
v___x_2023_ = l_Lean_Syntax_getArg(v___y_2008_, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_isNone(v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
lean_inc(v___x_2023_);
v___x_2025_ = l_Lean_Syntax_matchesNull(v___x_2023_, v___x_2006_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v___x_2023_);
lean_dec(v_o_2013_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2008_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2027_ = l_Lean_Syntax_getArg(v___x_2023_, v___x_1207_);
lean_dec(v___x_2023_);
v___x_2028_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
v___x_2029_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_2028_);
lean_inc(v___x_2027_);
v___x_2030_ = l_Lean_Syntax_isOfKind(v___x_2027_, v___x_2029_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v___x_2027_);
lean_dec(v_o_2013_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2008_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2031_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; lean_object* v_args_2033_; lean_object* v___x_2034_; 
v___x_2032_ = l_Lean_Syntax_getArg(v___x_2027_, v___x_2006_);
lean_dec(v___x_2027_);
v_args_2033_ = l_Lean_Syntax_getArgs(v___x_2032_);
lean_dec(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_args_2033_);
v___y_1979_ = v___y_2008_;
v___y_1980_ = v_o_2013_;
v___y_1981_ = v___y_2009_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2012_;
v_args_1985_ = v___x_2034_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2021_;
goto v___jp_1978_;
}
}
}
else
{
lean_object* v___x_2035_; 
lean_dec(v___x_2023_);
v___x_2035_ = lean_box(0);
v___y_1979_ = v___y_2008_;
v___y_1980_ = v_o_2013_;
v___y_1981_ = v___y_2009_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2012_;
v_args_1985_ = v___x_2035_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2021_;
goto v___jp_1978_;
}
}
v___jp_2036_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2046_ = lean_unsigned_to_nat(2u);
v___x_2047_ = l_Lean_Syntax_getArg(v_stx_1191_, v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
v___x_2049_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_2048_);
lean_inc(v___x_2047_);
v___x_2050_ = l_Lean_Syntax_isOfKind(v___x_2047_, v___x_2049_);
lean_dec(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec(v___x_2047_);
lean_dec(v_bang_2037_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2051_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2051_;
}
else
{
lean_object* v_cfg_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_cfg_2052_ = l_Lean_Syntax_getArg(v___x_2047_, v___x_1207_);
v___x_2053_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1193_);
v___x_2054_ = l_Lean_Name_mkStr4(v___x_1193_, v___x_1194_, v___x_1195_, v___x_2053_);
lean_inc(v_cfg_2052_);
v___x_2055_ = l_Lean_Syntax_isOfKind(v_cfg_2052_, v___x_2054_);
lean_dec(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v_cfg_2052_);
lean_dec(v___x_2047_);
lean_dec(v_bang_2037_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = l_Lean_Syntax_getArg(v___x_2047_, v___x_2006_);
v___x_2058_ = l_Lean_Syntax_getArg(v___x_2047_, v___x_2046_);
v___x_2059_ = l_Lean_Syntax_isNone(v___x_2058_);
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
lean_inc(v___x_2058_);
v___x_2060_ = l_Lean_Syntax_matchesNull(v___x_2058_, v___x_2006_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec(v___x_2058_);
lean_dec(v___x_2057_);
lean_dec(v_cfg_2052_);
lean_dec(v___x_2047_);
lean_dec(v_bang_2037_);
lean_dec(v_tk_1208_);
lean_dec_ref(v___f_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v___x_2061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2061_;
}
else
{
lean_object* v_o_2062_; lean_object* v___x_2063_; 
v_o_2062_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_1207_);
lean_dec(v___x_2058_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_o_2062_);
v___y_2008_ = v___x_2047_;
v___y_2009_ = v___x_2050_;
v___y_2010_ = v_bang_2037_;
v___y_2011_ = v_cfg_2052_;
v___y_2012_ = v___x_2057_;
v_o_2013_ = v___x_2063_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v___y_2021_ = v___y_2045_;
goto v___jp_2007_;
}
}
else
{
lean_object* v___x_2064_; 
lean_dec(v___x_2058_);
v___x_2064_ = lean_box(0);
v___y_2008_ = v___x_2047_;
v___y_2009_ = v___x_2050_;
v___y_2010_ = v_bang_2037_;
v___y_2011_ = v_cfg_2052_;
v___y_2012_ = v___x_2057_;
v_o_2013_ = v___x_2064_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v___y_2021_ = v___y_2045_;
goto v___jp_2007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2072_, lean_object* v_stx_2073_, lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v___f_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_35271__boxed_2088_; uint8_t v___x_35272__boxed_2089_; lean_object* v_res_2090_; 
v___x_35271__boxed_2088_ = lean_unbox(v___x_2072_);
v___x_35272__boxed_2089_ = lean_unbox(v___x_2074_);
v_res_2090_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35271__boxed_2088_, v_stx_2073_, v___x_35272__boxed_2089_, v___x_2075_, v___x_2076_, v___x_2077_, v___f_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v_stx_2073_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___y_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2113_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2100_);
v___x_2114_ = l_Lean_Syntax_isOfKind(v_stx_2100_, v___x_2113_);
v___x_2115_ = 1;
v___f_2116_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2117_ = lean_box(v___x_2114_);
v___x_2118_ = lean_box(v___x_2115_);
v___y_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2119_, 0, v___x_2117_);
lean_closure_set(v___y_2119_, 1, v_stx_2100_);
lean_closure_set(v___y_2119_, 2, v___x_2118_);
lean_closure_set(v___y_2119_, 3, v___x_2110_);
lean_closure_set(v___y_2119_, 4, v___x_2111_);
lean_closure_set(v___y_2119_, 5, v___x_2112_);
lean_closure_set(v___y_2119_, 6, v___f_2116_);
v___x_2120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2120_, 0, v___y_2119_);
v___x_2121_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2120_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2133_, lean_object* v_as_2134_, lean_object* v_as_x27_2135_, lean_object* v_b_2136_, lean_object* v_a_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2133_, v_as_x27_2135_, v_b_2136_, v___y_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2148_, lean_object* v_as_2149_, lean_object* v_as_x27_2150_, lean_object* v_b_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2148_, v_as_2149_, v_as_x27_2150_, v_b_2151_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_as_x27_2150_);
lean_dec(v_as_2149_);
lean_dec(v___x_2148_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2163_, lean_object* v_ref_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2164_, v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2176_, lean_object* v_ref_2177_, lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2176_, v_ref_2177_, v_msg_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v_ref_2177_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2189_, lean_object* v_ref_2190_, lean_object* v_constName_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2190_, v_constName_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_ref_2203_, lean_object* v_constName_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2202_, v_ref_2203_, v_constName_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v_ref_2203_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2215_, lean_object* v_msg_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2216_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_msg_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2227_, v_msg_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2239_, v___y_2246_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_opt_2250_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2261_, lean_object* v_ref_2262_, lean_object* v_msg_2263_, lean_object* v_declHint_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2262_, v_msg_2263_, v_declHint_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_ref_2276_, lean_object* v_msg_2277_, lean_object* v_declHint_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2275_, v_ref_2276_, v_msg_2277_, v_declHint_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v_ref_2276_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2289_, lean_object* v_declHint_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2289_, v_declHint_2290_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2301_, v_declHint_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2313_, lean_object* v_msgData_2314_, uint8_t v_severity_2315_, uint8_t v_isSilent_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2313_, v_msgData_2314_, v_severity_2315_, v_isSilent_2316_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2327_, lean_object* v_msgData_2328_, lean_object* v_severity_2329_, lean_object* v_isSilent_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v_severity_boxed_2340_; uint8_t v_isSilent_boxed_2341_; lean_object* v_res_2342_; 
v_severity_boxed_2340_ = lean_unbox(v_severity_2329_);
v_isSilent_boxed_2341_ = lean_unbox(v_isSilent_2330_);
v_res_2342_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2327_, v_msgData_2328_, v_severity_boxed_2340_, v_isSilent_boxed_2341_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_ref_2327_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2350_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2354_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2350_, v___x_2351_, v___x_2352_, v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2385_ = l_Lean_addBuiltinDeclarationRanges(v___x_2383_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2388_, lean_object* v_as_x27_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_){
_start:
{
if (lean_obj_tag(v_as_x27_2389_) == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_b_2390_);
return v___x_2393_;
}
else
{
lean_object* v_head_2394_; lean_object* v_tail_2395_; lean_object* v_ref_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_head_2394_ = lean_ctor_get(v_as_x27_2389_, 0);
v_tail_2395_ = lean_ctor_get(v_as_x27_2389_, 1);
v_ref_2396_ = lean_ctor_get(v___y_2391_, 2);
v___x_2397_ = 1;
v___x_2398_ = 0;
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_ref_2396_, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2401_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2402_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2399_);
v___x_2403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2399_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
lean_ctor_set(v___x_2403_, 2, v___x_2402_);
lean_inc(v_head_2394_);
v___x_2404_ = l_Lean_mkCIdentFrom(v___x_2388_, v_head_2394_, v___x_2397_);
lean_inc_ref(v___x_2403_);
v___x_2405_ = l_Lean_Syntax_node3(v___x_2399_, v___x_2400_, v___x_2403_, v___x_2403_, v___x_2404_);
v___x_2406_ = lean_array_push(v_b_2390_, v___x_2405_);
v_as_x27_2389_ = v_tail_2395_;
v_b_2390_ = v___x_2406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2408_, lean_object* v_as_x27_2409_, lean_object* v_b_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2408_, v_as_x27_2409_, v_b_2410_, v___y_2411_);
lean_dec_ref(v___y_2411_);
lean_dec(v_as_x27_2409_);
lean_dec(v___x_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2414_, size_t v_sz_2415_, size_t v_i_2416_, lean_object* v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_usize_dec_lt(v_i_2416_, v_sz_2415_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_b_2417_);
return v___x_2428_;
}
else
{
lean_object* v_a_2429_; lean_object* v_name_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2429_ = lean_array_uget_borrowed(v_as_2414_, v_i_2416_);
v_name_2430_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_name_2430_);
v___x_2431_ = l_Lean_mkIdent(v_name_2430_);
lean_inc(v___x_2431_);
v___x_2432_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2431_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2434_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2431_, v_a_2433_, v_b_2417_, v___y_2424_);
lean_dec(v_a_2433_);
lean_dec(v___x_2431_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; size_t v___x_2436_; size_t v___x_2437_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2416_, v___x_2436_);
v_i_2416_ = v___x_2437_;
v_b_2417_ = v_a_2435_;
goto _start;
}
else
{
return v___x_2434_;
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v___x_2431_);
lean_dec_ref(v_b_2417_);
v_a_2439_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2432_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2432_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2447_, lean_object* v_sz_2448_, lean_object* v_i_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
size_t v_sz_boxed_2460_; size_t v_i_boxed_2461_; lean_object* v_res_2462_; 
v_sz_boxed_2460_ = lean_unbox_usize(v_sz_2448_);
lean_dec(v_sz_2448_);
v_i_boxed_2461_ = lean_unbox_usize(v_i_2449_);
lean_dec(v_i_2449_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2447_, v_sz_boxed_2460_, v_i_boxed_2461_, v_b_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec_ref(v_as_2447_);
return v_res_2462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_unsigned_to_nat(32u);
v___x_2469_ = lean_mk_empty_array_with_capacity(v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2471_ = ((size_t)5ULL);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_unsigned_to_nat(32u);
v___x_2474_ = lean_mk_empty_array_with_capacity(v___x_2473_);
v___x_2475_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2476_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2474_);
lean_ctor_set(v___x_2476_, 2, v___x_2472_);
lean_ctor_set(v___x_2476_, 3, v___x_2472_);
lean_ctor_set_usize(v___x_2476_, 4, v___x_2471_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
lean_ctor_set(v___x_2479_, 2, v___x_2478_);
lean_ctor_set(v___x_2479_, 3, v___x_2477_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2481_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2491_, lean_object* v_stx_2492_, uint8_t v___x_2493_, lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v___f_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
if (v___x_2491_ == 0)
{
lean_object* v___x_2507_; 
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_2507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v_tk_2509_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2624_; uint8_t v___y_2625_; lean_object* v___y_2626_; uint8_t v___y_2627_; lean_object* v_stxForSuggestion_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; uint8_t v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; uint8_t v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; uint8_t v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; uint8_t v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; uint8_t v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; uint8_t v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; uint8_t v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; uint8_t v___y_2908_; uint8_t v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v_stxForExecution_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; uint8_t v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; uint8_t v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint8_t v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; uint8_t v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; uint8_t v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; uint8_t v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; uint8_t v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; uint8_t v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; uint8_t v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; uint8_t v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; uint8_t v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; uint8_t v___y_3240_; uint8_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; lean_object* v_argsArray_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; uint8_t v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; uint8_t v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; uint8_t v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v_args_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___x_3439_; uint8_t v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v_o_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v_bang_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_2508_ = lean_unsigned_to_nat(0u);
v_tk_2509_ = l_Lean_Syntax_getArg(v_stx_2492_, v___x_2508_);
v___x_3439_ = lean_unsigned_to_nat(1u);
v___x_3498_ = l_Lean_Syntax_getArg(v_stx_2492_, v___x_3439_);
v___x_3499_ = l_Lean_Syntax_isNone(v___x_3498_);
if (v___x_3499_ == 0)
{
uint8_t v___x_3500_; 
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Syntax_matchesNull(v___x_3498_, v___x_3439_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v___x_3498_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3501_;
}
else
{
lean_object* v_bang_3502_; lean_object* v___x_3503_; 
v_bang_3502_ = l_Lean_Syntax_getArg(v___x_3498_, v___x_2508_);
lean_dec(v___x_3498_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_bang_3502_);
v_bang_3470_ = v___x_3503_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
v___y_3476_ = v___y_2503_;
v___y_3477_ = v___y_2504_;
v___y_3478_ = v___y_2505_;
goto v___jp_3469_;
}
}
else
{
lean_object* v___x_3504_; 
lean_dec(v___x_3498_);
v___x_3504_ = lean_box(0);
v_bang_3470_ = v___x_3504_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
v___y_3476_ = v___y_2503_;
v___y_3477_ = v___y_2504_;
v___y_3478_ = v___y_2505_;
goto v___jp_3469_;
}
v___jp_2510_:
{
lean_object* v_usedTheorems_2517_; lean_object* v_diag_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2560_; 
v_usedTheorems_2517_ = lean_ctor_get(v___y_2511_, 0);
v_diag_2518_ = lean_ctor_get(v___y_2511_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___y_2511_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2520_ = v___y_2511_;
v_isShared_2521_ = v_isSharedCheck_2560_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_diag_2518_);
lean_inc(v_usedTheorems_2517_);
lean_dec(v___y_2511_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2560_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2512_, v_usedTheorems_2517_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec_ref(v_usedTheorems_2517_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v_ref_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
v_ref_2524_ = lean_ctor_get(v___y_2515_, 2);
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 1, v_a_2523_);
lean_ctor_set(v___x_2520_, 0, v___x_2525_);
v___x_2527_ = v___x_2520_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_a_2523_);
v___x_2527_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
lean_ctor_set(v___x_2529_, 2, v___x_2528_);
lean_ctor_set(v___x_2529_, 3, v___x_2528_);
lean_ctor_set(v___x_2529_, 4, v___x_2528_);
lean_ctor_set(v___x_2529_, 5, v___x_2528_);
lean_inc(v_ref_2524_);
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_ref_2524_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2532_ = 4;
v___x_2533_ = l_Lean_MessageData_nil;
v___x_2534_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2509_, v___x_2529_, v___x_2530_, v___x_2531_, v___x_2528_, v___x_2532_, v___x_2533_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v___x_2534_, 0);
lean_dec(v_unused_2542_);
v___x_2536_ = v___x_2534_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_dec(v___x_2534_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v_diag_2518_);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_diag_2518_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_diag_2518_);
v_a_2543_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2534_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2534_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_del_object(v___x_2520_);
lean_dec_ref(v_diag_2518_);
lean_dec(v_tk_2509_);
v_a_2552_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2522_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2522_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
v___jp_2561_:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2565_, v___y_2564_, v___y_2568_, v___y_2563_, v___y_2567_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2573_ = l_Lean_Meta_simpAll(v_a_2571_, v___y_2569_, v___y_2562_, v___x_2572_, v___y_2564_, v___y_2568_, v___y_2563_, v___y_2567_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_fst_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v_fst_2575_ = lean_ctor_get(v_a_2574_, 0);
if (lean_obj_tag(v_fst_2575_) == 0)
{
lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_snd_2576_ = lean_ctor_get(v_a_2574_, 1);
lean_inc(v_snd_2576_);
lean_dec(v_a_2574_);
v___x_2577_ = lean_box(0);
v___x_2578_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2577_, v___y_2565_, v___y_2564_, v___y_2568_, v___y_2563_, v___y_2567_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_dec_ref_known(v___x_2578_, 1);
v___y_2511_ = v_snd_2576_;
v___y_2512_ = v___y_2566_;
v___y_2513_ = v___y_2564_;
v___y_2514_ = v___y_2568_;
v___y_2515_ = v___y_2563_;
v___y_2516_ = v___y_2567_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_snd_2576_);
lean_dec(v___y_2566_);
lean_dec(v_tk_2509_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2605_; 
lean_inc_ref(v_fst_2575_);
v_snd_2587_ = lean_ctor_get(v_a_2574_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_a_2574_, 0);
lean_dec(v_unused_2606_);
v___x_2589_ = v_a_2574_;
v_isShared_2590_ = v_isSharedCheck_2605_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_dec(v_a_2574_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2605_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_val_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v_val_2591_ = lean_ctor_get(v_fst_2575_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v_fst_2575_, 1);
v___x_2592_ = lean_box(0);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
lean_ctor_set(v___x_2589_, 1, v___x_2592_);
lean_ctor_set(v___x_2589_, 0, v_val_2591_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_val_2591_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2594_, v___y_2565_, v___y_2564_, v___y_2568_, v___y_2563_, v___y_2567_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
v___y_2511_ = v_snd_2587_;
v___y_2512_ = v___y_2566_;
v___y_2513_ = v___y_2564_;
v___y_2514_ = v___y_2568_;
v___y_2515_ = v___y_2563_;
v___y_2516_ = v___y_2567_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_snd_2587_);
lean_dec(v___y_2566_);
lean_dec(v_tk_2509_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v___y_2566_);
lean_dec(v_tk_2509_);
v_a_2607_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2573_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2573_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2562_);
lean_dec(v_tk_2509_);
v_a_2615_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2570_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2570_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
v___jp_2623_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2638_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2624_, v___x_2493_, v___y_2627_, v___x_2493_, v___x_2637_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2624_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
if (lean_obj_tag(v___y_2626_) == 0)
{
lean_object* v_ctx_2640_; lean_object* v_simprocs_2641_; 
v_ctx_2640_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_ctx_2640_);
v_simprocs_2641_ = lean_ctor_get(v_a_2639_, 1);
lean_inc_ref(v_simprocs_2641_);
lean_dec(v_a_2639_);
v___y_2562_ = v_simprocs_2641_;
v___y_2563_ = v___y_2635_;
v___y_2564_ = v___y_2633_;
v___y_2565_ = v___y_2630_;
v___y_2566_ = v_stxForSuggestion_2628_;
v___y_2567_ = v___y_2636_;
v___y_2568_ = v___y_2634_;
v___y_2569_ = v_ctx_2640_;
goto v___jp_2561_;
}
else
{
lean_dec_ref_known(v___y_2626_, 1);
if (v___y_2625_ == 0)
{
lean_object* v_ctx_2642_; lean_object* v_simprocs_2643_; 
v_ctx_2642_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_ctx_2642_);
v_simprocs_2643_ = lean_ctor_get(v_a_2639_, 1);
lean_inc_ref(v_simprocs_2643_);
lean_dec(v_a_2639_);
v___y_2562_ = v_simprocs_2643_;
v___y_2563_ = v___y_2635_;
v___y_2564_ = v___y_2633_;
v___y_2565_ = v___y_2630_;
v___y_2566_ = v_stxForSuggestion_2628_;
v___y_2567_ = v___y_2636_;
v___y_2568_ = v___y_2634_;
v___y_2569_ = v_ctx_2642_;
goto v___jp_2561_;
}
else
{
lean_object* v_ctx_2644_; lean_object* v_simprocs_2645_; lean_object* v___x_2646_; 
v_ctx_2644_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_ctx_2644_);
v_simprocs_2645_ = lean_ctor_get(v_a_2639_, 1);
lean_inc_ref(v_simprocs_2645_);
lean_dec(v_a_2639_);
v___x_2646_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2644_);
v___y_2562_ = v_simprocs_2645_;
v___y_2563_ = v___y_2635_;
v___y_2564_ = v___y_2633_;
v___y_2565_ = v___y_2630_;
v___y_2566_ = v_stxForSuggestion_2628_;
v___y_2567_ = v___y_2636_;
v___y_2568_ = v___y_2634_;
v___y_2569_ = v___x_2646_;
goto v___jp_2561_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_stxForSuggestion_2628_);
lean_dec(v___y_2626_);
lean_dec(v_tk_2509_);
v_a_2647_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2638_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2638_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
v___jp_2655_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_inc_ref_n(v___y_2672_, 2);
v___x_2677_ = l_Array_append___redArg(v___y_2672_, v___y_2676_);
lean_dec_ref(v___y_2676_);
lean_inc_n(v___y_2674_, 3);
lean_inc_n(v___y_2662_, 5);
v___x_2678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2678_, 0, v___y_2662_);
lean_ctor_set(v___x_2678_, 1, v___y_2674_);
lean_ctor_set(v___x_2678_, 2, v___x_2677_);
v___x_2679_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___y_2662_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2682_ = l_Lean_Syntax_SepArray_ofElems(v___x_2681_, v___y_2658_);
lean_dec_ref(v___y_2658_);
v___x_2683_ = l_Array_append___redArg(v___y_2672_, v___x_2682_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2662_);
lean_ctor_set(v___x_2684_, 1, v___y_2674_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2662_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node3(v___y_2662_, v___y_2674_, v___x_2680_, v___x_2684_, v___x_2686_);
v___x_2688_ = l_Lean_Syntax_node5(v___y_2662_, v___y_2660_, v___y_2669_, v___y_2663_, v___y_2675_, v___x_2678_, v___x_2687_);
v___y_2624_ = v___y_2656_;
v___y_2625_ = v___y_2666_;
v___y_2626_ = v___y_2671_;
v___y_2627_ = v___y_2673_;
v_stxForSuggestion_2628_ = v___x_2688_;
v___y_2629_ = v___y_2661_;
v___y_2630_ = v___y_2670_;
v___y_2631_ = v___y_2657_;
v___y_2632_ = v___y_2665_;
v___y_2633_ = v___y_2659_;
v___y_2634_ = v___y_2667_;
v___y_2635_ = v___y_2668_;
v___y_2636_ = v___y_2664_;
goto v___jp_2623_;
}
v___jp_2689_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_inc_ref(v___y_2707_);
v___x_2711_ = l_Array_append___redArg(v___y_2707_, v___y_2710_);
lean_dec_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc(v___y_2697_);
v___x_2712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___y_2697_);
lean_ctor_set(v___x_2712_, 1, v___y_2709_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
if (lean_obj_tag(v___y_2692_) == 1)
{
lean_object* v_val_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_val_2713_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v___y_2692_, 1);
v___x_2714_ = l_Lean_SourceInfo_fromRef(v_val_2713_, v___x_2493_);
lean_dec(v_val_2713_);
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Array_mkArray1___redArg(v___x_2716_);
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2693_;
v___y_2659_ = v___y_2694_;
v___y_2660_ = v___y_2695_;
v___y_2661_ = v___y_2696_;
v___y_2662_ = v___y_2697_;
v___y_2663_ = v___y_2698_;
v___y_2664_ = v___y_2699_;
v___y_2665_ = v___y_2700_;
v___y_2666_ = v___y_2701_;
v___y_2667_ = v___y_2702_;
v___y_2668_ = v___y_2703_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___y_2707_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___x_2712_;
v___y_2676_ = v___x_2717_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2718_; 
lean_dec(v___y_2692_);
v___x_2718_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2693_;
v___y_2659_ = v___y_2694_;
v___y_2660_ = v___y_2695_;
v___y_2661_ = v___y_2696_;
v___y_2662_ = v___y_2697_;
v___y_2663_ = v___y_2698_;
v___y_2664_ = v___y_2699_;
v___y_2665_ = v___y_2700_;
v___y_2666_ = v___y_2701_;
v___y_2667_ = v___y_2702_;
v___y_2668_ = v___y_2703_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___y_2707_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___x_2712_;
v___y_2676_ = v___x_2718_;
goto v___jp_2655_;
}
}
v___jp_2719_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_inc_ref_n(v___y_2739_, 2);
v___x_2741_ = l_Array_append___redArg(v___y_2739_, v___y_2740_);
lean_dec_ref(v___y_2740_);
lean_inc_n(v___y_2732_, 3);
lean_inc_n(v___y_2730_, 5);
v___x_2742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2730_);
lean_ctor_set(v___x_2742_, 1, v___y_2732_);
lean_ctor_set(v___x_2742_, 2, v___x_2741_);
v___x_2743_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___y_2730_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2746_ = l_Lean_Syntax_SepArray_ofElems(v___x_2745_, v___y_2723_);
lean_dec_ref(v___y_2723_);
v___x_2747_ = l_Array_append___redArg(v___y_2739_, v___x_2746_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___y_2730_);
lean_ctor_set(v___x_2748_, 1, v___y_2732_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2730_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Lean_Syntax_node3(v___y_2730_, v___y_2732_, v___x_2744_, v___x_2748_, v___x_2750_);
v___x_2752_ = l_Lean_Syntax_node5(v___y_2730_, v___y_2731_, v___y_2722_, v___y_2727_, v___y_2725_, v___x_2742_, v___x_2751_);
v___y_2624_ = v___y_2720_;
v___y_2625_ = v___y_2733_;
v___y_2626_ = v___y_2737_;
v___y_2627_ = v___y_2738_;
v_stxForSuggestion_2628_ = v___x_2752_;
v___y_2629_ = v___y_2726_;
v___y_2630_ = v___y_2736_;
v___y_2631_ = v___y_2721_;
v___y_2632_ = v___y_2729_;
v___y_2633_ = v___y_2724_;
v___y_2634_ = v___y_2734_;
v___y_2635_ = v___y_2735_;
v___y_2636_ = v___y_2728_;
goto v___jp_2623_;
}
v___jp_2753_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_inc_ref(v___y_2773_);
v___x_2775_ = l_Array_append___redArg(v___y_2773_, v___y_2774_);
lean_dec_ref(v___y_2774_);
lean_inc(v___y_2766_);
lean_inc(v___y_2764_);
v___x_2776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2764_);
lean_ctor_set(v___x_2776_, 1, v___y_2766_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
if (lean_obj_tag(v___y_2756_) == 1)
{
lean_object* v_val_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_val_2777_ = lean_ctor_get(v___y_2756_, 0);
lean_inc(v_val_2777_);
lean_dec_ref_known(v___y_2756_, 1);
v___x_2778_ = l_Lean_SourceInfo_fromRef(v_val_2777_, v___x_2493_);
lean_dec(v_val_2777_);
v___x_2779_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = l_Array_mkArray1___redArg(v___x_2780_);
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2757_;
v___y_2723_ = v___y_2758_;
v___y_2724_ = v___y_2759_;
v___y_2725_ = v___x_2776_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___x_2781_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2782_; 
lean_dec(v___y_2756_);
v___x_2782_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2757_;
v___y_2723_ = v___y_2758_;
v___y_2724_ = v___y_2759_;
v___y_2725_ = v___x_2776_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___x_2782_;
goto v___jp_2719_;
}
}
v___jp_2783_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_inc_ref_n(v___y_2787_, 2);
v___x_2804_ = l_Array_append___redArg(v___y_2787_, v___y_2803_);
lean_dec_ref(v___y_2803_);
lean_inc_n(v___y_2784_, 2);
lean_inc_n(v___y_2785_, 2);
v___x_2805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2805_, 0, v___y_2785_);
lean_ctor_set(v___x_2805_, 1, v___y_2784_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
v___x_2806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2806_, 0, v___y_2785_);
lean_ctor_set(v___x_2806_, 1, v___y_2784_);
lean_ctor_set(v___x_2806_, 2, v___y_2787_);
v___x_2807_ = l_Lean_Syntax_node5(v___y_2785_, v___y_2788_, v___y_2789_, v___y_2794_, v___y_2791_, v___x_2805_, v___x_2806_);
v___y_2624_ = v___y_2786_;
v___y_2625_ = v___y_2797_;
v___y_2626_ = v___y_2801_;
v___y_2627_ = v___y_2802_;
v_stxForSuggestion_2628_ = v___x_2807_;
v___y_2629_ = v___y_2793_;
v___y_2630_ = v___y_2800_;
v___y_2631_ = v___y_2790_;
v___y_2632_ = v___y_2796_;
v___y_2633_ = v___y_2792_;
v___y_2634_ = v___y_2798_;
v___y_2635_ = v___y_2799_;
v___y_2636_ = v___y_2795_;
goto v___jp_2623_;
}
v___jp_2808_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_inc_ref(v___y_2811_);
v___x_2829_ = l_Array_append___redArg(v___y_2811_, v___y_2828_);
lean_dec_ref(v___y_2828_);
lean_inc(v___y_2809_);
lean_inc(v___y_2810_);
v___x_2830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2830_, 0, v___y_2810_);
lean_ctor_set(v___x_2830_, 1, v___y_2809_);
lean_ctor_set(v___x_2830_, 2, v___x_2829_);
if (lean_obj_tag(v___y_2816_) == 1)
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_val_2831_ = lean_ctor_get(v___y_2816_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v___y_2816_, 1);
v___x_2832_ = l_Lean_SourceInfo_fromRef(v_val_2831_, v___x_2493_);
lean_dec(v_val_2831_);
v___x_2833_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l_Array_mkArray1___redArg(v___x_2834_);
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2812_;
v___y_2787_ = v___y_2811_;
v___y_2788_ = v___y_2813_;
v___y_2789_ = v___y_2814_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___x_2830_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2818_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2820_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2825_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___y_2827_;
v___y_2803_ = v___x_2835_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2836_; 
lean_dec(v___y_2816_);
v___x_2836_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2812_;
v___y_2787_ = v___y_2811_;
v___y_2788_ = v___y_2813_;
v___y_2789_ = v___y_2814_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___x_2830_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2818_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2820_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2825_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___y_2827_;
v___y_2803_ = v___x_2836_;
goto v___jp_2783_;
}
}
v___jp_2837_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_inc_ref_n(v___y_2848_, 2);
v___x_2858_ = l_Array_append___redArg(v___y_2848_, v___y_2857_);
lean_dec_ref(v___y_2857_);
lean_inc_n(v___y_2851_, 2);
lean_inc_n(v___y_2847_, 2);
v___x_2859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___y_2847_);
lean_ctor_set(v___x_2859_, 1, v___y_2851_);
lean_ctor_set(v___x_2859_, 2, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2847_);
lean_ctor_set(v___x_2860_, 1, v___y_2851_);
lean_ctor_set(v___x_2860_, 2, v___y_2848_);
v___x_2861_ = l_Lean_Syntax_node5(v___y_2847_, v___y_2856_, v___y_2838_, v___y_2843_, v___y_2844_, v___x_2859_, v___x_2860_);
v___y_2624_ = v___y_2839_;
v___y_2625_ = v___y_2849_;
v___y_2626_ = v___y_2854_;
v___y_2627_ = v___y_2855_;
v_stxForSuggestion_2628_ = v___x_2861_;
v___y_2629_ = v___y_2842_;
v___y_2630_ = v___y_2853_;
v___y_2631_ = v___y_2840_;
v___y_2632_ = v___y_2846_;
v___y_2633_ = v___y_2841_;
v___y_2634_ = v___y_2850_;
v___y_2635_ = v___y_2852_;
v___y_2636_ = v___y_2845_;
goto v___jp_2623_;
}
v___jp_2862_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref(v___y_2873_);
v___x_2883_ = l_Array_append___redArg(v___y_2873_, v___y_2882_);
lean_dec_ref(v___y_2882_);
lean_inc(v___y_2876_);
lean_inc(v___y_2872_);
v___x_2884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2884_, 0, v___y_2872_);
lean_ctor_set(v___x_2884_, 1, v___y_2876_);
lean_ctor_set(v___x_2884_, 2, v___x_2883_);
if (lean_obj_tag(v___y_2866_) == 1)
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_val_2885_ = lean_ctor_get(v___y_2866_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v___y_2866_, 1);
v___x_2886_ = l_Lean_SourceInfo_fromRef(v_val_2885_, v___x_2493_);
lean_dec(v_val_2885_);
v___x_2887_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Array_mkArray1___redArg(v___x_2888_);
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2864_;
v___y_2840_ = v___y_2865_;
v___y_2841_ = v___y_2867_;
v___y_2842_ = v___y_2868_;
v___y_2843_ = v___y_2869_;
v___y_2844_ = v___x_2884_;
v___y_2845_ = v___y_2870_;
v___y_2846_ = v___y_2871_;
v___y_2847_ = v___y_2872_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2874_;
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2880_;
v___y_2857_ = v___x_2889_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2890_; 
lean_dec(v___y_2866_);
v___x_2890_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2864_;
v___y_2840_ = v___y_2865_;
v___y_2841_ = v___y_2867_;
v___y_2842_ = v___y_2868_;
v___y_2843_ = v___y_2869_;
v___y_2844_ = v___x_2884_;
v___y_2845_ = v___y_2870_;
v___y_2846_ = v___y_2871_;
v___y_2847_ = v___y_2872_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2874_;
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2880_;
v___y_2857_ = v___x_2890_;
goto v___jp_2837_;
}
}
v___jp_2891_:
{
lean_object* v_ref_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_ref_2909_ = lean_ctor_get(v___y_2903_, 2);
v___x_2910_ = l_Lean_SourceInfo_fromRef(v_ref_2909_, v___y_2908_);
v___x_2911_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2912_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_2911_);
v___x_2913_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2917_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2904_) == 1)
{
lean_object* v_val_2918_; lean_object* v___x_2919_; 
v_val_2918_ = lean_ctor_get(v___y_2904_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v___y_2904_, 1);
v___x_2919_ = l_Array_mkArray1___redArg(v_val_2918_);
v___y_2690_ = v___y_2892_;
v___y_2691_ = v___y_2893_;
v___y_2692_ = v___y_2894_;
v___y_2693_ = v___y_2895_;
v___y_2694_ = v___y_2896_;
v___y_2695_ = v___x_2912_;
v___y_2696_ = v___y_2897_;
v___y_2697_ = v___x_2910_;
v___y_2698_ = v___y_2898_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2902_;
v___y_2703_ = v___y_2903_;
v___y_2704_ = v___y_2905_;
v___y_2705_ = v___x_2915_;
v___y_2706_ = v___y_2906_;
v___y_2707_ = v___x_2917_;
v___y_2708_ = v___y_2907_;
v___y_2709_ = v___x_2916_;
v___y_2710_ = v___x_2919_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2920_; 
lean_dec(v___y_2904_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2690_ = v___y_2892_;
v___y_2691_ = v___y_2893_;
v___y_2692_ = v___y_2894_;
v___y_2693_ = v___y_2895_;
v___y_2694_ = v___y_2896_;
v___y_2695_ = v___x_2912_;
v___y_2696_ = v___y_2897_;
v___y_2697_ = v___x_2910_;
v___y_2698_ = v___y_2898_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2902_;
v___y_2703_ = v___y_2903_;
v___y_2704_ = v___y_2905_;
v___y_2705_ = v___x_2915_;
v___y_2706_ = v___y_2906_;
v___y_2707_ = v___x_2917_;
v___y_2708_ = v___y_2907_;
v___y_2709_ = v___x_2916_;
v___y_2710_ = v___x_2920_;
goto v___jp_2689_;
}
}
v___jp_2921_:
{
lean_object* v___x_2938_; lean_object* v_a_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2938_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2926_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = lean_array_get_size(v___y_2924_);
v___x_2941_ = lean_nat_dec_eq(v___x_2940_, v___x_2508_);
if (v___x_2941_ == 0)
{
if (lean_obj_tag(v___y_2927_) == 0)
{
v___y_2892_ = v_stxForExecution_2929_;
v___y_2893_ = v___y_2932_;
v___y_2894_ = v___y_2923_;
v___y_2895_ = v___y_2924_;
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v_a_2939_;
v___y_2899_ = v___y_2937_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___y_2936_;
v___y_2904_ = v___y_2925_;
v___y_2905_ = v___y_2931_;
v___y_2906_ = v___y_2927_;
v___y_2907_ = v___y_2928_;
v___y_2908_ = v___x_2941_;
goto v___jp_2891_;
}
else
{
if (v___y_2922_ == 0)
{
v___y_2892_ = v_stxForExecution_2929_;
v___y_2893_ = v___y_2932_;
v___y_2894_ = v___y_2923_;
v___y_2895_ = v___y_2924_;
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v_a_2939_;
v___y_2899_ = v___y_2937_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___y_2936_;
v___y_2904_ = v___y_2925_;
v___y_2905_ = v___y_2931_;
v___y_2906_ = v___y_2927_;
v___y_2907_ = v___y_2928_;
v___y_2908_ = v___y_2922_;
goto v___jp_2891_;
}
else
{
lean_object* v_ref_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_ref_2942_ = lean_ctor_get(v___y_2936_, 2);
v___x_2943_ = l_Lean_SourceInfo_fromRef(v_ref_2942_, v___x_2941_);
v___x_2944_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2945_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_2944_);
v___x_2946_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_2947_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2950_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2925_) == 1)
{
lean_object* v_val_2951_; lean_object* v___x_2952_; 
v_val_2951_ = lean_ctor_get(v___y_2925_, 0);
lean_inc(v_val_2951_);
lean_dec_ref_known(v___y_2925_, 1);
v___x_2952_ = l_Array_mkArray1___redArg(v_val_2951_);
v___y_2754_ = v_stxForExecution_2929_;
v___y_2755_ = v___y_2932_;
v___y_2756_ = v___y_2923_;
v___y_2757_ = v___x_2948_;
v___y_2758_ = v___y_2924_;
v___y_2759_ = v___y_2934_;
v___y_2760_ = v___y_2930_;
v___y_2761_ = v_a_2939_;
v___y_2762_ = v___y_2937_;
v___y_2763_ = v___y_2933_;
v___y_2764_ = v___x_2943_;
v___y_2765_ = v___x_2945_;
v___y_2766_ = v___x_2949_;
v___y_2767_ = v___y_2922_;
v___y_2768_ = v___y_2935_;
v___y_2769_ = v___y_2936_;
v___y_2770_ = v___y_2931_;
v___y_2771_ = v___y_2927_;
v___y_2772_ = v___y_2928_;
v___y_2773_ = v___x_2950_;
v___y_2774_ = v___x_2952_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2953_; 
lean_dec(v___y_2925_);
v___x_2953_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2754_ = v_stxForExecution_2929_;
v___y_2755_ = v___y_2932_;
v___y_2756_ = v___y_2923_;
v___y_2757_ = v___x_2948_;
v___y_2758_ = v___y_2924_;
v___y_2759_ = v___y_2934_;
v___y_2760_ = v___y_2930_;
v___y_2761_ = v_a_2939_;
v___y_2762_ = v___y_2937_;
v___y_2763_ = v___y_2933_;
v___y_2764_ = v___x_2943_;
v___y_2765_ = v___x_2945_;
v___y_2766_ = v___x_2949_;
v___y_2767_ = v___y_2922_;
v___y_2768_ = v___y_2935_;
v___y_2769_ = v___y_2936_;
v___y_2770_ = v___y_2931_;
v___y_2771_ = v___y_2927_;
v___y_2772_ = v___y_2928_;
v___y_2773_ = v___x_2950_;
v___y_2774_ = v___x_2953_;
goto v___jp_2753_;
}
}
}
}
else
{
lean_dec_ref(v___y_2924_);
if (lean_obj_tag(v___y_2927_) == 0)
{
lean_object* v_ref_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_ref_2954_ = lean_ctor_get(v___y_2936_, 2);
v___x_2955_ = 0;
v___x_2956_ = l_Lean_SourceInfo_fromRef(v_ref_2954_, v___x_2955_);
v___x_2957_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2958_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_2957_);
v___x_2959_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_2960_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2963_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2925_) == 1)
{
lean_object* v_val_2964_; lean_object* v___x_2965_; 
v_val_2964_ = lean_ctor_get(v___y_2925_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v___y_2925_, 1);
v___x_2965_ = l_Array_mkArray1___redArg(v_val_2964_);
v___y_2809_ = v___x_2962_;
v___y_2810_ = v___x_2956_;
v___y_2811_ = v___x_2963_;
v___y_2812_ = v_stxForExecution_2929_;
v___y_2813_ = v___x_2958_;
v___y_2814_ = v___x_2961_;
v___y_2815_ = v___y_2932_;
v___y_2816_ = v___y_2923_;
v___y_2817_ = v___y_2934_;
v___y_2818_ = v___y_2930_;
v___y_2819_ = v_a_2939_;
v___y_2820_ = v___y_2937_;
v___y_2821_ = v___y_2933_;
v___y_2822_ = v___y_2922_;
v___y_2823_ = v___y_2935_;
v___y_2824_ = v___y_2936_;
v___y_2825_ = v___y_2931_;
v___y_2826_ = v___y_2927_;
v___y_2827_ = v___y_2928_;
v___y_2828_ = v___x_2965_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2966_; 
lean_dec(v___y_2925_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2809_ = v___x_2962_;
v___y_2810_ = v___x_2956_;
v___y_2811_ = v___x_2963_;
v___y_2812_ = v_stxForExecution_2929_;
v___y_2813_ = v___x_2958_;
v___y_2814_ = v___x_2961_;
v___y_2815_ = v___y_2932_;
v___y_2816_ = v___y_2923_;
v___y_2817_ = v___y_2934_;
v___y_2818_ = v___y_2930_;
v___y_2819_ = v_a_2939_;
v___y_2820_ = v___y_2937_;
v___y_2821_ = v___y_2933_;
v___y_2822_ = v___y_2922_;
v___y_2823_ = v___y_2935_;
v___y_2824_ = v___y_2936_;
v___y_2825_ = v___y_2931_;
v___y_2826_ = v___y_2927_;
v___y_2827_ = v___y_2928_;
v___y_2828_ = v___x_2966_;
goto v___jp_2808_;
}
}
else
{
lean_object* v_ref_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_ref_2967_ = lean_ctor_get(v___y_2936_, 2);
v___x_2968_ = 0;
v___x_2969_ = l_Lean_SourceInfo_fromRef(v_ref_2967_, v___x_2968_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2971_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_2970_);
v___x_2972_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2976_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2925_) == 1)
{
lean_object* v_val_2977_; lean_object* v___x_2978_; 
v_val_2977_ = lean_ctor_get(v___y_2925_, 0);
lean_inc(v_val_2977_);
lean_dec_ref_known(v___y_2925_, 1);
v___x_2978_ = l_Array_mkArray1___redArg(v_val_2977_);
v___y_2863_ = v___x_2974_;
v___y_2864_ = v_stxForExecution_2929_;
v___y_2865_ = v___y_2932_;
v___y_2866_ = v___y_2923_;
v___y_2867_ = v___y_2934_;
v___y_2868_ = v___y_2930_;
v___y_2869_ = v_a_2939_;
v___y_2870_ = v___y_2937_;
v___y_2871_ = v___y_2933_;
v___y_2872_ = v___x_2969_;
v___y_2873_ = v___x_2976_;
v___y_2874_ = v___y_2922_;
v___y_2875_ = v___y_2935_;
v___y_2876_ = v___x_2975_;
v___y_2877_ = v___y_2936_;
v___y_2878_ = v___y_2931_;
v___y_2879_ = v___y_2927_;
v___y_2880_ = v___x_2971_;
v___y_2881_ = v___y_2928_;
v___y_2882_ = v___x_2978_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2979_; 
lean_dec(v___y_2925_);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2863_ = v___x_2974_;
v___y_2864_ = v_stxForExecution_2929_;
v___y_2865_ = v___y_2932_;
v___y_2866_ = v___y_2923_;
v___y_2867_ = v___y_2934_;
v___y_2868_ = v___y_2930_;
v___y_2869_ = v_a_2939_;
v___y_2870_ = v___y_2937_;
v___y_2871_ = v___y_2933_;
v___y_2872_ = v___x_2969_;
v___y_2873_ = v___x_2976_;
v___y_2874_ = v___y_2922_;
v___y_2875_ = v___y_2935_;
v___y_2876_ = v___x_2975_;
v___y_2877_ = v___y_2936_;
v___y_2878_ = v___y_2931_;
v___y_2879_ = v___y_2927_;
v___y_2880_ = v___x_2971_;
v___y_2881_ = v___y_2928_;
v___y_2882_ = v___x_2979_;
goto v___jp_2862_;
}
}
}
}
v___jp_2980_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_inc_ref_n(v___y_2985_, 2);
v___x_3003_ = l_Array_append___redArg(v___y_2985_, v___y_3002_);
lean_dec_ref(v___y_3002_);
lean_inc_n(v___y_2993_, 3);
lean_inc_n(v___y_2982_, 5);
v___x_3004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3004_, 0, v___y_2982_);
lean_ctor_set(v___x_3004_, 1, v___y_2993_);
lean_ctor_set(v___x_3004_, 2, v___x_3003_);
v___x_3005_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___y_2982_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3008_ = l_Lean_Syntax_SepArray_ofElems(v___x_3007_, v___y_2986_);
v___x_3009_ = l_Array_append___redArg(v___y_2985_, v___x_3008_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3010_, 0, v___y_2982_);
lean_ctor_set(v___x_3010_, 1, v___y_2993_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___y_2982_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = l_Lean_Syntax_node3(v___y_2982_, v___y_2993_, v___x_3006_, v___x_3010_, v___x_3012_);
lean_inc(v___y_2987_);
v___x_3014_ = l_Lean_Syntax_node5(v___y_2982_, v___y_2995_, v___y_2983_, v___y_2987_, v___y_2989_, v___x_3004_, v___x_3013_);
v___y_2922_ = v___y_2992_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2986_;
v___y_2925_ = v___y_2994_;
v___y_2926_ = v___y_2987_;
v___y_2927_ = v___y_2997_;
v___y_2928_ = v___y_3001_;
v_stxForExecution_2929_ = v___x_3014_;
v___y_2930_ = v___y_2981_;
v___y_2931_ = v___y_2988_;
v___y_2932_ = v___y_3000_;
v___y_2933_ = v___y_2996_;
v___y_2934_ = v___y_2991_;
v___y_2935_ = v___y_2999_;
v___y_2936_ = v___y_2990_;
v___y_2937_ = v___y_2998_;
goto v___jp_2921_;
}
v___jp_3015_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_inc_ref(v___y_3019_);
v___x_3037_ = l_Array_append___redArg(v___y_3019_, v___y_3036_);
lean_dec_ref(v___y_3036_);
lean_inc(v___y_3027_);
lean_inc(v___y_3017_);
v___x_3038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3038_, 0, v___y_3017_);
lean_ctor_set(v___x_3038_, 1, v___y_3027_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
if (lean_obj_tag(v___y_3020_) == 1)
{
lean_object* v_val_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_val_3039_ = lean_ctor_get(v___y_3020_, 0);
v___x_3040_ = l_Lean_SourceInfo_fromRef(v_val_3039_, v___x_2493_);
v___x_3041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Array_mkArray1___redArg(v___x_3042_);
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3020_;
v___y_2985_ = v___y_3019_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___x_3038_;
v___y_2990_ = v___y_3024_;
v___y_2991_ = v___y_3025_;
v___y_2992_ = v___y_3026_;
v___y_2993_ = v___y_3027_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3029_;
v___y_2997_ = v___y_3034_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3031_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___x_3043_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3020_;
v___y_2985_ = v___y_3019_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___x_3038_;
v___y_2990_ = v___y_3024_;
v___y_2991_ = v___y_3025_;
v___y_2992_ = v___y_3026_;
v___y_2993_ = v___y_3027_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3029_;
v___y_2997_ = v___y_3034_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3031_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___x_3044_;
goto v___jp_2980_;
}
}
v___jp_3045_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_ref_n(v___y_3050_, 2);
v___x_3068_ = l_Array_append___redArg(v___y_3050_, v___y_3067_);
lean_dec_ref(v___y_3067_);
lean_inc_n(v___y_3055_, 3);
lean_inc_n(v___y_3048_, 5);
v___x_3069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___y_3048_);
lean_ctor_set(v___x_3069_, 1, v___y_3055_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
v___x_3070_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3048_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3073_ = l_Lean_Syntax_SepArray_ofElems(v___x_3072_, v___y_3051_);
v___x_3074_ = l_Array_append___redArg(v___y_3050_, v___x_3073_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3075_, 0, v___y_3048_);
lean_ctor_set(v___x_3075_, 1, v___y_3055_);
lean_ctor_set(v___x_3075_, 2, v___x_3074_);
v___x_3076_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3048_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_Syntax_node3(v___y_3048_, v___y_3055_, v___x_3071_, v___x_3075_, v___x_3077_);
lean_inc(v___y_3052_);
v___x_3079_ = l_Lean_Syntax_node5(v___y_3048_, v___y_3056_, v___y_3054_, v___y_3052_, v___y_3047_, v___x_3069_, v___x_3078_);
v___y_2922_ = v___y_3059_;
v___y_2923_ = v___y_3049_;
v___y_2924_ = v___y_3051_;
v___y_2925_ = v___y_3060_;
v___y_2926_ = v___y_3052_;
v___y_2927_ = v___y_3062_;
v___y_2928_ = v___y_3066_;
v_stxForExecution_2929_ = v___x_3079_;
v___y_2930_ = v___y_3046_;
v___y_2931_ = v___y_3053_;
v___y_2932_ = v___y_3065_;
v___y_2933_ = v___y_3061_;
v___y_2934_ = v___y_3058_;
v___y_2935_ = v___y_3064_;
v___y_2936_ = v___y_3057_;
v___y_2937_ = v___y_3063_;
goto v___jp_2921_;
}
v___jp_3080_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_inc_ref(v___y_3084_);
v___x_3102_ = l_Array_append___redArg(v___y_3084_, v___y_3101_);
lean_dec_ref(v___y_3101_);
lean_inc(v___y_3089_);
lean_inc(v___y_3082_);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3082_);
lean_ctor_set(v___x_3103_, 1, v___y_3089_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
if (lean_obj_tag(v___y_3083_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_val_3104_ = lean_ctor_get(v___y_3083_, 0);
v___x_3105_ = l_Lean_SourceInfo_fromRef(v_val_3104_, v___x_2493_);
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Array_mkArray1___redArg(v___x_3107_);
v___y_3046_ = v___y_3081_;
v___y_3047_ = v___x_3103_;
v___y_3048_ = v___y_3082_;
v___y_3049_ = v___y_3083_;
v___y_3050_ = v___y_3084_;
v___y_3051_ = v___y_3085_;
v___y_3052_ = v___y_3086_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3096_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___x_3108_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3109_; 
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3046_ = v___y_3081_;
v___y_3047_ = v___x_3103_;
v___y_3048_ = v___y_3082_;
v___y_3049_ = v___y_3083_;
v___y_3050_ = v___y_3084_;
v___y_3051_ = v___y_3085_;
v___y_3052_ = v___y_3086_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3096_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___x_3109_;
goto v___jp_3045_;
}
}
v___jp_3110_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_inc_ref_n(v___y_3126_, 2);
v___x_3133_ = l_Array_append___redArg(v___y_3126_, v___y_3132_);
lean_dec_ref(v___y_3132_);
lean_inc_n(v___y_3131_, 2);
lean_inc_n(v___y_3127_, 2);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___y_3127_);
lean_ctor_set(v___x_3134_, 1, v___y_3131_);
lean_ctor_set(v___x_3134_, 2, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3135_, 0, v___y_3127_);
lean_ctor_set(v___x_3135_, 1, v___y_3131_);
lean_ctor_set(v___x_3135_, 2, v___y_3126_);
lean_inc(v___y_3115_);
v___x_3136_ = l_Lean_Syntax_node5(v___y_3127_, v___y_3121_, v___y_3119_, v___y_3115_, v___y_3112_, v___x_3134_, v___x_3135_);
v___y_2922_ = v___y_3120_;
v___y_2923_ = v___y_3113_;
v___y_2924_ = v___y_3114_;
v___y_2925_ = v___y_3122_;
v___y_2926_ = v___y_3115_;
v___y_2927_ = v___y_3124_;
v___y_2928_ = v___y_3130_;
v_stxForExecution_2929_ = v___x_3136_;
v___y_2930_ = v___y_3111_;
v___y_2931_ = v___y_3116_;
v___y_2932_ = v___y_3128_;
v___y_2933_ = v___y_3123_;
v___y_2934_ = v___y_3118_;
v___y_2935_ = v___y_3129_;
v___y_2936_ = v___y_3117_;
v___y_2937_ = v___y_3125_;
goto v___jp_2921_;
}
v___jp_3137_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_inc_ref(v___y_3154_);
v___x_3159_ = l_Array_append___redArg(v___y_3154_, v___y_3158_);
lean_dec_ref(v___y_3158_);
lean_inc(v___y_3157_);
lean_inc(v___y_3155_);
v___x_3160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3155_);
lean_ctor_set(v___x_3160_, 1, v___y_3157_);
lean_ctor_set(v___x_3160_, 2, v___x_3159_);
if (lean_obj_tag(v___y_3139_) == 1)
{
lean_object* v_val_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_val_3161_ = lean_ctor_get(v___y_3139_, 0);
v___x_3162_ = l_Lean_SourceInfo_fromRef(v_val_3161_, v___x_2493_);
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Array_mkArray1___redArg(v___x_3164_);
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3160_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3145_;
v___y_3120_ = v___y_3146_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3153_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3150_;
v___y_3130_ = v___y_3156_;
v___y_3131_ = v___y_3157_;
v___y_3132_ = v___x_3165_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3166_; 
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3160_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3145_;
v___y_3120_ = v___y_3146_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3153_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3150_;
v___y_3130_ = v___y_3156_;
v___y_3131_ = v___y_3157_;
v___y_3132_ = v___x_3166_;
goto v___jp_3110_;
}
}
v___jp_3167_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_inc_ref_n(v___y_3180_, 2);
v___x_3190_ = l_Array_append___redArg(v___y_3180_, v___y_3189_);
lean_dec_ref(v___y_3189_);
lean_inc_n(v___y_3172_, 2);
lean_inc_n(v___y_3181_, 2);
v___x_3191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3181_);
lean_ctor_set(v___x_3191_, 1, v___y_3172_);
lean_ctor_set(v___x_3191_, 2, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___y_3181_);
lean_ctor_set(v___x_3192_, 1, v___y_3172_);
lean_ctor_set(v___x_3192_, 2, v___y_3180_);
lean_inc(v___y_3173_);
v___x_3193_ = l_Lean_Syntax_node5(v___y_3181_, v___y_3168_, v___y_3177_, v___y_3173_, v___y_3175_, v___x_3191_, v___x_3192_);
v___y_2922_ = v___y_3179_;
v___y_2923_ = v___y_3170_;
v___y_2924_ = v___y_3171_;
v___y_2925_ = v___y_3182_;
v___y_2926_ = v___y_3173_;
v___y_2927_ = v___y_3184_;
v___y_2928_ = v___y_3188_;
v_stxForExecution_2929_ = v___x_3193_;
v___y_2930_ = v___y_3169_;
v___y_2931_ = v___y_3174_;
v___y_2932_ = v___y_3186_;
v___y_2933_ = v___y_3183_;
v___y_2934_ = v___y_3178_;
v___y_2935_ = v___y_3187_;
v___y_2936_ = v___y_3176_;
v___y_2937_ = v___y_3185_;
goto v___jp_2921_;
}
v___jp_3194_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc_ref(v___y_3206_);
v___x_3216_ = l_Array_append___redArg(v___y_3206_, v___y_3215_);
lean_dec_ref(v___y_3215_);
lean_inc(v___y_3199_);
lean_inc(v___y_3207_);
v___x_3217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3217_, 0, v___y_3207_);
lean_ctor_set(v___x_3217_, 1, v___y_3199_);
lean_ctor_set(v___x_3217_, 2, v___x_3216_);
if (lean_obj_tag(v___y_3197_) == 1)
{
lean_object* v_val_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_val_3218_ = lean_ctor_get(v___y_3197_, 0);
v___x_3219_ = l_Lean_SourceInfo_fromRef(v_val_3218_, v___x_2493_);
v___x_3220_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Array_mkArray1___redArg(v___x_3221_);
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3196_;
v___y_3170_ = v___y_3197_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___x_3217_;
v___y_3176_ = v___y_3202_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3204_;
v___y_3179_ = v___y_3205_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3213_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3211_;
v___y_3187_ = v___y_3210_;
v___y_3188_ = v___y_3214_;
v___y_3189_ = v___x_3222_;
goto v___jp_3167_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3196_;
v___y_3170_ = v___y_3197_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___x_3217_;
v___y_3176_ = v___y_3202_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3204_;
v___y_3179_ = v___y_3205_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3213_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3211_;
v___y_3187_ = v___y_3210_;
v___y_3188_ = v___y_3214_;
v___y_3189_ = v___x_3223_;
goto v___jp_3167_;
}
}
v___jp_3224_:
{
lean_object* v_ref_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_ref_3241_ = lean_ctor_get(v___y_3230_, 2);
v___x_3242_ = l_Lean_SourceInfo_fromRef(v_ref_3241_, v___y_3240_);
v___x_3243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3244_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3243_);
v___x_3245_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_3246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3249_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3233_) == 1)
{
lean_object* v_val_3250_; lean_object* v___x_3251_; 
v_val_3250_ = lean_ctor_get(v___y_3233_, 0);
lean_inc(v_val_3250_);
v___x_3251_ = l_Array_mkArray1___redArg(v_val_3250_);
v___y_3016_ = v___y_3225_;
v___y_3017_ = v___x_3242_;
v___y_3018_ = v___x_3247_;
v___y_3019_ = v___x_3249_;
v___y_3020_ = v___y_3226_;
v___y_3021_ = v___y_3227_;
v___y_3022_ = v___y_3228_;
v___y_3023_ = v___y_3229_;
v___y_3024_ = v___y_3230_;
v___y_3025_ = v___y_3231_;
v___y_3026_ = v___y_3232_;
v___y_3027_ = v___x_3248_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___x_3244_;
v___y_3031_ = v___y_3237_;
v___y_3032_ = v___y_3238_;
v___y_3033_ = v___y_3236_;
v___y_3034_ = v___y_3235_;
v___y_3035_ = v___y_3239_;
v___y_3036_ = v___x_3251_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3016_ = v___y_3225_;
v___y_3017_ = v___x_3242_;
v___y_3018_ = v___x_3247_;
v___y_3019_ = v___x_3249_;
v___y_3020_ = v___y_3226_;
v___y_3021_ = v___y_3227_;
v___y_3022_ = v___y_3228_;
v___y_3023_ = v___y_3229_;
v___y_3024_ = v___y_3230_;
v___y_3025_ = v___y_3231_;
v___y_3026_ = v___y_3232_;
v___y_3027_ = v___x_3248_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___x_3244_;
v___y_3031_ = v___y_3237_;
v___y_3032_ = v___y_3238_;
v___y_3033_ = v___y_3236_;
v___y_3034_ = v___y_3235_;
v___y_3035_ = v___y_3239_;
v___y_3036_ = v___x_3252_;
goto v___jp_3015_;
}
}
v___jp_3253_:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_array_get_size(v_argsArray_3260_);
v___x_3270_ = lean_nat_dec_eq(v___x_3269_, v___x_2508_);
if (v___x_3270_ == 0)
{
if (lean_obj_tag(v___y_3258_) == 0)
{
v___y_3225_ = v___y_3261_;
v___y_3226_ = v___y_3255_;
v___y_3227_ = v_argsArray_3260_;
v___y_3228_ = v___y_3256_;
v___y_3229_ = v___y_3262_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3265_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3258_;
v___y_3236_ = v___y_3268_;
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3266_;
v___y_3239_ = v___y_3259_;
v___y_3240_ = v___x_3270_;
goto v___jp_3224_;
}
else
{
if (v___y_3254_ == 0)
{
v___y_3225_ = v___y_3261_;
v___y_3226_ = v___y_3255_;
v___y_3227_ = v_argsArray_3260_;
v___y_3228_ = v___y_3256_;
v___y_3229_ = v___y_3262_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3265_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3258_;
v___y_3236_ = v___y_3268_;
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3266_;
v___y_3239_ = v___y_3259_;
v___y_3240_ = v___y_3254_;
goto v___jp_3224_;
}
else
{
lean_object* v_ref_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_ref_3271_ = lean_ctor_get(v___y_3267_, 2);
v___x_3272_ = l_Lean_SourceInfo_fromRef(v_ref_3271_, v___x_3270_);
v___x_3273_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3274_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3273_);
v___x_3275_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_3276_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3279_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3257_) == 1)
{
lean_object* v_val_3280_; lean_object* v___x_3281_; 
v_val_3280_ = lean_ctor_get(v___y_3257_, 0);
lean_inc(v_val_3280_);
v___x_3281_ = l_Array_mkArray1___redArg(v_val_3280_);
v___y_3081_ = v___y_3261_;
v___y_3082_ = v___x_3272_;
v___y_3083_ = v___y_3255_;
v___y_3084_ = v___x_3279_;
v___y_3085_ = v_argsArray_3260_;
v___y_3086_ = v___y_3256_;
v___y_3087_ = v___y_3262_;
v___y_3088_ = v___x_3277_;
v___y_3089_ = v___x_3278_;
v___y_3090_ = v___x_3274_;
v___y_3091_ = v___y_3267_;
v___y_3092_ = v___y_3265_;
v___y_3093_ = v___y_3254_;
v___y_3094_ = v___y_3257_;
v___y_3095_ = v___y_3264_;
v___y_3096_ = v___y_3263_;
v___y_3097_ = v___y_3266_;
v___y_3098_ = v___y_3268_;
v___y_3099_ = v___y_3258_;
v___y_3100_ = v___y_3259_;
v___y_3101_ = v___x_3281_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3081_ = v___y_3261_;
v___y_3082_ = v___x_3272_;
v___y_3083_ = v___y_3255_;
v___y_3084_ = v___x_3279_;
v___y_3085_ = v_argsArray_3260_;
v___y_3086_ = v___y_3256_;
v___y_3087_ = v___y_3262_;
v___y_3088_ = v___x_3277_;
v___y_3089_ = v___x_3278_;
v___y_3090_ = v___x_3274_;
v___y_3091_ = v___y_3267_;
v___y_3092_ = v___y_3265_;
v___y_3093_ = v___y_3254_;
v___y_3094_ = v___y_3257_;
v___y_3095_ = v___y_3264_;
v___y_3096_ = v___y_3263_;
v___y_3097_ = v___y_3266_;
v___y_3098_ = v___y_3268_;
v___y_3099_ = v___y_3258_;
v___y_3100_ = v___y_3259_;
v___y_3101_ = v___x_3282_;
goto v___jp_3080_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3258_) == 0)
{
lean_object* v_ref_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_ref_3283_ = lean_ctor_get(v___y_3267_, 2);
v___x_3284_ = 0;
v___x_3285_ = l_Lean_SourceInfo_fromRef(v_ref_3283_, v___x_3284_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3287_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3286_);
v___x_3288_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_3289_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3292_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3257_) == 1)
{
lean_object* v_val_3293_; lean_object* v___x_3294_; 
v_val_3293_ = lean_ctor_get(v___y_3257_, 0);
lean_inc(v_val_3293_);
v___x_3294_ = l_Array_mkArray1___redArg(v_val_3293_);
v___y_3138_ = v___y_3261_;
v___y_3139_ = v___y_3255_;
v___y_3140_ = v_argsArray_3260_;
v___y_3141_ = v___y_3256_;
v___y_3142_ = v___y_3262_;
v___y_3143_ = v___y_3267_;
v___y_3144_ = v___y_3265_;
v___y_3145_ = v___x_3290_;
v___y_3146_ = v___y_3254_;
v___y_3147_ = v___x_3287_;
v___y_3148_ = v___y_3257_;
v___y_3149_ = v___y_3264_;
v___y_3150_ = v___y_3266_;
v___y_3151_ = v___y_3263_;
v___y_3152_ = v___y_3268_;
v___y_3153_ = v___y_3258_;
v___y_3154_ = v___x_3292_;
v___y_3155_ = v___x_3285_;
v___y_3156_ = v___y_3259_;
v___y_3157_ = v___x_3291_;
v___y_3158_ = v___x_3294_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3138_ = v___y_3261_;
v___y_3139_ = v___y_3255_;
v___y_3140_ = v_argsArray_3260_;
v___y_3141_ = v___y_3256_;
v___y_3142_ = v___y_3262_;
v___y_3143_ = v___y_3267_;
v___y_3144_ = v___y_3265_;
v___y_3145_ = v___x_3290_;
v___y_3146_ = v___y_3254_;
v___y_3147_ = v___x_3287_;
v___y_3148_ = v___y_3257_;
v___y_3149_ = v___y_3264_;
v___y_3150_ = v___y_3266_;
v___y_3151_ = v___y_3263_;
v___y_3152_ = v___y_3268_;
v___y_3153_ = v___y_3258_;
v___y_3154_ = v___x_3292_;
v___y_3155_ = v___x_3285_;
v___y_3156_ = v___y_3259_;
v___y_3157_ = v___x_3291_;
v___y_3158_ = v___x_3295_;
goto v___jp_3137_;
}
}
else
{
lean_object* v_ref_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_ref_3296_ = lean_ctor_get(v___y_3267_, 2);
v___x_3297_ = 0;
v___x_3298_ = l_Lean_SourceInfo_fromRef(v_ref_3296_, v___x_3297_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3300_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3299_);
v___x_3301_ = l_Lean_SourceInfo_fromRef(v_tk_2509_, v___x_2493_);
v___x_3302_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3305_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3257_) == 1)
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___y_3257_, 0);
lean_inc(v_val_3306_);
v___x_3307_ = l_Array_mkArray1___redArg(v_val_3306_);
v___y_3195_ = v___x_3300_;
v___y_3196_ = v___y_3261_;
v___y_3197_ = v___y_3255_;
v___y_3198_ = v_argsArray_3260_;
v___y_3199_ = v___x_3304_;
v___y_3200_ = v___y_3256_;
v___y_3201_ = v___y_3262_;
v___y_3202_ = v___y_3267_;
v___y_3203_ = v___x_3303_;
v___y_3204_ = v___y_3265_;
v___y_3205_ = v___y_3254_;
v___y_3206_ = v___x_3305_;
v___y_3207_ = v___x_3298_;
v___y_3208_ = v___y_3257_;
v___y_3209_ = v___y_3264_;
v___y_3210_ = v___y_3266_;
v___y_3211_ = v___y_3263_;
v___y_3212_ = v___y_3268_;
v___y_3213_ = v___y_3258_;
v___y_3214_ = v___y_3259_;
v___y_3215_ = v___x_3307_;
goto v___jp_3194_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3195_ = v___x_3300_;
v___y_3196_ = v___y_3261_;
v___y_3197_ = v___y_3255_;
v___y_3198_ = v_argsArray_3260_;
v___y_3199_ = v___x_3304_;
v___y_3200_ = v___y_3256_;
v___y_3201_ = v___y_3262_;
v___y_3202_ = v___y_3267_;
v___y_3203_ = v___x_3303_;
v___y_3204_ = v___y_3265_;
v___y_3205_ = v___y_3254_;
v___y_3206_ = v___x_3305_;
v___y_3207_ = v___x_3298_;
v___y_3208_ = v___y_3257_;
v___y_3209_ = v___y_3264_;
v___y_3210_ = v___y_3266_;
v___y_3211_ = v___y_3263_;
v___y_3212_ = v___y_3268_;
v___y_3213_ = v___y_3258_;
v___y_3214_ = v___y_3259_;
v___y_3215_ = v___x_3308_;
goto v___jp_3194_;
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3312_, v___y_3316_, v___y_3310_, v___y_3311_, v___y_3322_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l_Lean_LibrarySuggestions_select(v_a_3327_, v___y_3325_, v___y_3316_, v___y_3310_, v___y_3311_, v___y_3322_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; size_t v_sz_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v_sz_3330_ = lean_array_size(v_a_3329_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3329_, v_sz_3330_, v___x_3331_, v___y_3315_, v___y_3317_, v___y_3312_, v___y_3320_, v___y_3318_, v___y_3316_, v___y_3310_, v___y_3311_, v___y_3322_);
lean_dec(v_a_3329_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___y_3254_ = v___y_3319_;
v___y_3255_ = v___y_3313_;
v___y_3256_ = v___y_3314_;
v___y_3257_ = v___y_3321_;
v___y_3258_ = v___y_3323_;
v___y_3259_ = v___y_3324_;
v_argsArray_3260_ = v_a_3333_;
v___y_3261_ = v___y_3317_;
v___y_3262_ = v___y_3312_;
v___y_3263_ = v___y_3320_;
v___y_3264_ = v___y_3318_;
v___y_3265_ = v___y_3316_;
v___y_3266_ = v___y_3310_;
v___y_3267_ = v___y_3311_;
v___y_3268_ = v___y_3322_;
goto v___jp_3253_;
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___y_3323_);
lean_dec(v___y_3321_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v_a_3334_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3332_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3332_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v___y_3323_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v_a_3342_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3328_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3328_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3323_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v_a_3350_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3326_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3326_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
v___jp_3358_:
{
lean_object* v_config_3375_; uint8_t v_suggestions_3376_; 
v_config_3375_ = lean_ctor_get(v___y_3366_, 0);
lean_inc_ref(v_config_3375_);
lean_dec_ref(v___y_3366_);
v_suggestions_3376_ = lean_ctor_get_uint8(v_config_3375_, sizeof(void*)*3 + 26);
if (v_suggestions_3376_ == 0)
{
lean_dec_ref(v_config_3375_);
lean_dec_ref(v___f_2497_);
v___y_3254_ = v___y_3368_;
v___y_3255_ = v___y_3362_;
v___y_3256_ = v___y_3363_;
v___y_3257_ = v___y_3370_;
v___y_3258_ = v___y_3372_;
v___y_3259_ = v___y_3373_;
v_argsArray_3260_ = v___y_3374_;
v___y_3261_ = v___y_3365_;
v___y_3262_ = v___y_3361_;
v___y_3263_ = v___y_3369_;
v___y_3264_ = v___y_3367_;
v___y_3265_ = v___y_3364_;
v___y_3266_ = v___y_3359_;
v___y_3267_ = v___y_3360_;
v___y_3268_ = v___y_3371_;
goto v___jp_3253_;
}
else
{
lean_object* v_maxSuggestions_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_maxSuggestions_3377_ = lean_ctor_get(v_config_3375_, 2);
lean_inc(v_maxSuggestions_3377_);
lean_dec_ref(v_config_3375_);
v___x_3378_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3379_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3377_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_unsigned_to_nat(100u);
v___x_3381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___x_3378_);
lean_ctor_set(v___x_3381_, 2, v___f_2497_);
lean_ctor_set(v___x_3381_, 3, v___x_3379_);
v___y_3310_ = v___y_3359_;
v___y_3311_ = v___y_3360_;
v___y_3312_ = v___y_3361_;
v___y_3313_ = v___y_3362_;
v___y_3314_ = v___y_3363_;
v___y_3315_ = v___y_3374_;
v___y_3316_ = v___y_3364_;
v___y_3317_ = v___y_3365_;
v___y_3318_ = v___y_3367_;
v___y_3319_ = v___y_3368_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___x_3381_;
goto v___jp_3309_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3383_; 
v_val_3382_ = lean_ctor_get(v_maxSuggestions_3377_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_maxSuggestions_3377_, 1);
v___x_3383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3383_, 0, v_val_3382_);
lean_ctor_set(v___x_3383_, 1, v___x_3378_);
lean_ctor_set(v___x_3383_, 2, v___f_2497_);
lean_ctor_set(v___x_3383_, 3, v___x_3379_);
v___y_3310_ = v___y_3359_;
v___y_3311_ = v___y_3360_;
v___y_3312_ = v___y_3361_;
v___y_3313_ = v___y_3362_;
v___y_3314_ = v___y_3363_;
v___y_3315_ = v___y_3374_;
v___y_3316_ = v___y_3364_;
v___y_3317_ = v___y_3365_;
v___y_3318_ = v___y_3367_;
v___y_3319_ = v___y_3368_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___x_3383_;
goto v___jp_3309_;
}
}
}
v___jp_3384_:
{
uint8_t v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = 1;
lean_inc(v___y_3389_);
v___x_3400_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3389_, v___x_3399_, v___y_3391_, v___y_3386_, v___y_3396_);
if (lean_obj_tag(v___x_3400_) == 0)
{
if (lean_obj_tag(v___y_3390_) == 1)
{
lean_object* v_a_3401_; lean_object* v_val_3402_; lean_object* v___x_3403_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v_val_3402_ = lean_ctor_get(v___y_3390_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v___y_3390_, 1);
v___x_3403_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3402_);
lean_dec(v_val_3402_);
v___y_3359_ = v___y_3385_;
v___y_3360_ = v___y_3386_;
v___y_3361_ = v___y_3388_;
v___y_3362_ = v___y_3387_;
v___y_3363_ = v___y_3389_;
v___y_3364_ = v___y_3392_;
v___y_3365_ = v___y_3391_;
v___y_3366_ = v_a_3401_;
v___y_3367_ = v___y_3393_;
v___y_3368_ = v___y_3394_;
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3398_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3397_;
v___y_3373_ = v___x_3399_;
v___y_3374_ = v___x_3403_;
goto v___jp_3358_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3405_; 
lean_dec(v___y_3390_);
v_a_3404_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3405_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3359_ = v___y_3385_;
v___y_3360_ = v___y_3386_;
v___y_3361_ = v___y_3388_;
v___y_3362_ = v___y_3387_;
v___y_3363_ = v___y_3389_;
v___y_3364_ = v___y_3392_;
v___y_3365_ = v___y_3391_;
v___y_3366_ = v_a_3404_;
v___y_3367_ = v___y_3393_;
v___y_3368_ = v___y_3394_;
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3398_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3397_;
v___y_3373_ = v___x_3399_;
v___y_3374_ = v___x_3405_;
goto v___jp_3358_;
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v___y_3387_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v_a_3406_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3400_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3400_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
v___jp_3414_:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Syntax_getOptional_x3f(v___y_3418_);
lean_dec(v___y_3418_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_box(0);
v___y_3385_ = v___y_3426_;
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3416_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3417_;
v___y_3390_ = v_args_3420_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3425_;
v___y_3393_ = v___y_3424_;
v___y_3394_ = v___y_3415_;
v___y_3395_ = v___y_3423_;
v___y_3396_ = v___y_3428_;
v___y_3397_ = v___y_3419_;
v___y_3398_ = v___x_3430_;
goto v___jp_3384_;
}
else
{
lean_object* v_val_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_val_3431_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3429_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_val_3431_);
lean_dec(v___x_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_val_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
v___y_3385_ = v___y_3426_;
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3416_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3417_;
v___y_3390_ = v_args_3420_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3425_;
v___y_3393_ = v___y_3424_;
v___y_3394_ = v___y_3415_;
v___y_3395_ = v___y_3423_;
v___y_3396_ = v___y_3428_;
v___y_3397_ = v___y_3419_;
v___y_3398_ = v___x_3436_;
goto v___jp_3384_;
}
}
}
}
v___jp_3440_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = lean_unsigned_to_nat(3u);
v___x_3456_ = l_Lean_Syntax_getArg(v___y_3445_, v___x_3455_);
lean_dec(v___y_3445_);
v___x_3457_ = l_Lean_Syntax_isNone(v___x_3456_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
lean_inc(v___x_3456_);
v___x_3458_ = l_Lean_Syntax_matchesNull(v___x_3456_, v___x_3439_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; 
lean_dec(v___x_3456_);
lean_dec(v_o_3446_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3460_ = l_Lean_Syntax_getArg(v___x_3456_, v___x_2508_);
lean_dec(v___x_3456_);
v___x_3461_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3462_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3461_);
lean_inc(v___x_3460_);
v___x_3463_ = l_Lean_Syntax_isOfKind(v___x_3460_, v___x_3462_);
lean_dec(v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
lean_dec(v___x_3460_);
lean_dec(v_o_3446_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; lean_object* v_args_3466_; lean_object* v___x_3467_; 
v___x_3465_ = l_Lean_Syntax_getArg(v___x_3460_, v___x_3439_);
lean_dec(v___x_3460_);
v_args_3466_ = l_Lean_Syntax_getArgs(v___x_3465_);
lean_dec(v___x_3465_);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_args_3466_);
v___y_3415_ = v___y_3441_;
v___y_3416_ = v_o_3446_;
v___y_3417_ = v___y_3442_;
v___y_3418_ = v___y_3444_;
v___y_3419_ = v___y_3443_;
v_args_3420_ = v___x_3467_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
v___y_3426_ = v___y_3452_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___y_3454_;
goto v___jp_3414_;
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec(v___x_3456_);
v___x_3468_ = lean_box(0);
v___y_3415_ = v___y_3441_;
v___y_3416_ = v_o_3446_;
v___y_3417_ = v___y_3442_;
v___y_3418_ = v___y_3444_;
v___y_3419_ = v___y_3443_;
v_args_3420_ = v___x_3468_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
v___y_3426_ = v___y_3452_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___y_3454_;
goto v___jp_3414_;
}
}
v___jp_3469_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3479_ = lean_unsigned_to_nat(2u);
v___x_3480_ = l_Lean_Syntax_getArg(v_stx_2492_, v___x_3479_);
v___x_3481_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3482_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3481_);
lean_inc(v___x_3480_);
v___x_3483_ = l_Lean_Syntax_isOfKind(v___x_3480_, v___x_3482_);
lean_dec(v___x_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_dec(v___x_3480_);
lean_dec(v_bang_3470_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3484_;
}
else
{
lean_object* v_cfg_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v_cfg_3485_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_2508_);
v___x_3486_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2496_);
lean_inc_ref(v___x_2495_);
lean_inc_ref(v___x_2494_);
v___x_3487_ = l_Lean_Name_mkStr4(v___x_2494_, v___x_2495_, v___x_2496_, v___x_3486_);
lean_inc(v_cfg_3485_);
v___x_3488_ = l_Lean_Syntax_isOfKind(v_cfg_3485_, v___x_3487_);
lean_dec(v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_dec(v_cfg_3485_);
lean_dec(v___x_3480_);
lean_dec(v_bang_3470_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3489_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3439_);
v___x_3491_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3479_);
v___x_3492_ = l_Lean_Syntax_isNone(v___x_3491_);
if (v___x_3492_ == 0)
{
uint8_t v___x_3493_; 
lean_inc(v___x_3491_);
v___x_3493_ = l_Lean_Syntax_matchesNull(v___x_3491_, v___x_3439_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
lean_dec(v___x_3491_);
lean_dec(v___x_3490_);
lean_dec(v_cfg_3485_);
lean_dec(v___x_3480_);
lean_dec(v_bang_3470_);
lean_dec(v_tk_2509_);
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___x_2494_);
v___x_3494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3494_;
}
else
{
lean_object* v_o_3495_; lean_object* v___x_3496_; 
v_o_3495_ = l_Lean_Syntax_getArg(v___x_3491_, v___x_2508_);
lean_dec(v___x_3491_);
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_o_3495_);
v___y_3441_ = v___x_3483_;
v___y_3442_ = v_cfg_3485_;
v___y_3443_ = v_bang_3470_;
v___y_3444_ = v___x_3490_;
v___y_3445_ = v___x_3480_;
v_o_3446_ = v___x_3496_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
v___y_3452_ = v___y_3476_;
v___y_3453_ = v___y_3477_;
v___y_3454_ = v___y_3478_;
goto v___jp_3440_;
}
}
else
{
lean_object* v___x_3497_; 
lean_dec(v___x_3491_);
v___x_3497_ = lean_box(0);
v___y_3441_ = v___x_3483_;
v___y_3442_ = v_cfg_3485_;
v___y_3443_ = v_bang_3470_;
v___y_3444_ = v___x_3490_;
v___y_3445_ = v___x_3480_;
v_o_3446_ = v___x_3497_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
v___y_3452_ = v___y_3476_;
v___y_3453_ = v___y_3477_;
v___y_3454_ = v___y_3478_;
goto v___jp_3440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3505_, lean_object* v_stx_3506_, lean_object* v___x_3507_, lean_object* v___x_3508_, lean_object* v___x_3509_, lean_object* v___x_3510_, lean_object* v___f_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v___x_31073__boxed_3521_; uint8_t v___x_31074__boxed_3522_; lean_object* v_res_3523_; 
v___x_31073__boxed_3521_ = lean_unbox(v___x_3505_);
v___x_31074__boxed_3522_ = lean_unbox(v___x_3507_);
v_res_3523_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31073__boxed_3521_, v_stx_3506_, v___x_31074__boxed_3522_, v___x_3508_, v___x_3509_, v___x_3510_, v___f_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v_stx_3506_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; uint8_t v___x_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___y_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3543_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3530_);
v___x_3544_ = l_Lean_Syntax_isOfKind(v_stx_3530_, v___x_3543_);
v___x_3545_ = 1;
v___f_3546_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3547_ = lean_box(v___x_3544_);
v___x_3548_ = lean_box(v___x_3545_);
v___y_3549_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3549_, 0, v___x_3547_);
lean_closure_set(v___y_3549_, 1, v_stx_3530_);
lean_closure_set(v___y_3549_, 2, v___x_3548_);
lean_closure_set(v___y_3549_, 3, v___x_3540_);
lean_closure_set(v___y_3549_, 4, v___x_3541_);
lean_closure_set(v___y_3549_, 5, v___x_3542_);
lean_closure_set(v___y_3549_, 6, v___f_3546_);
v___x_3550_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3550_, 0, v___y_3549_);
v___x_3551_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3550_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3563_, lean_object* v_as_3564_, lean_object* v_as_x27_3565_, lean_object* v_b_3566_, lean_object* v_a_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3563_, v_as_x27_3565_, v_b_3566_, v___y_3574_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3578_, lean_object* v_as_3579_, lean_object* v_as_x27_3580_, lean_object* v_b_3581_, lean_object* v_a_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3578_, v_as_3579_, v_as_x27_3580_, v_b_3581_, v_a_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v_as_x27_3580_);
lean_dec(v_as_3579_);
lean_dec(v___x_3578_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3600_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3603_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3604_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3600_, v___x_3601_, v___x_3602_, v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3634_ = l_Lean_addBuiltinDeclarationRanges(v___x_3632_, v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3637_, lean_object* v_simprocs_3638_, lean_object* v_fvarIdsToSimp_3639_, uint8_t v_simplifyTarget_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3647_, 1);
v___x_3649_ = lean_unsigned_to_nat(32u);
v___x_3650_ = lean_mk_empty_array_with_capacity(v___x_3649_);
lean_dec_ref(v___x_3650_);
v___x_3651_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3652_ = l_Lean_Meta_dsimpGoal(v_a_3648_, v_ctx_3637_, v_simprocs_3638_, v_simplifyTarget_3640_, v_fvarIdsToSimp_3639_, v___x_3651_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v_fst_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v_fst_3654_ = lean_ctor_get(v_a_3653_, 0);
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v_snd_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_snd_3655_ = lean_ctor_get(v_a_3653_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_a_3653_);
v___x_3656_ = lean_box(0);
v___x_3657_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3656_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; 
v_unused_3665_ = lean_ctor_get(v___x_3657_, 0);
lean_dec(v_unused_3665_);
v___x_3659_ = v___x_3657_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_dec(v___x_3657_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v_snd_3655_);
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_snd_3655_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_snd_3655_);
v_a_3666_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3657_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3657_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_snd_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3700_; 
lean_inc_ref(v_fst_3654_);
v_snd_3674_ = lean_ctor_get(v_a_3653_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_a_3653_);
if (v_isSharedCheck_3700_ == 0)
{
lean_object* v_unused_3701_; 
v_unused_3701_ = lean_ctor_get(v_a_3653_, 0);
lean_dec(v_unused_3701_);
v___x_3676_ = v_a_3653_;
v_isShared_3677_ = v_isSharedCheck_3700_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_snd_3674_);
lean_dec(v_a_3653_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3700_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_val_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v_val_3678_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3678_);
lean_dec_ref_known(v_fst_3654_, 1);
v___x_3679_ = lean_box(0);
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 1);
lean_ctor_set(v___x_3676_, 1, v___x_3679_);
lean_ctor_set(v___x_3676_, 0, v_val_3678_);
v___x_3681_ = v___x_3676_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_val_3678_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3681_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3682_, 0);
lean_dec(v_unused_3690_);
v___x_3684_ = v___x_3682_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v___x_3682_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_snd_3674_);
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_snd_3674_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_snd_3674_);
v_a_3691_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3682_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3682_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_a_3702_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3652_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3652_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v_fvarIdsToSimp_3639_);
lean_dec_ref(v_simprocs_3638_);
lean_dec_ref(v_ctx_3637_);
v_a_3710_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3647_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3647_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3718_, lean_object* v_simprocs_3719_, lean_object* v_fvarIdsToSimp_3720_, lean_object* v_simplifyTarget_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
uint8_t v_simplifyTarget_boxed_3728_; lean_object* v_res_3729_; 
v_simplifyTarget_boxed_3728_ = lean_unbox(v_simplifyTarget_3721_);
v_res_3729_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3718_, v_simprocs_3719_, v_fvarIdsToSimp_3720_, v_simplifyTarget_boxed_3728_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3730_, lean_object* v_simprocs_3731_, lean_object* v_fvarIdsToSimp_3732_, uint8_t v_simplifyTarget_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3730_, v_simprocs_3731_, v_fvarIdsToSimp_3732_, v_simplifyTarget_3733_, v_a_3735_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3744_, lean_object* v_simprocs_3745_, lean_object* v_fvarIdsToSimp_3746_, lean_object* v_simplifyTarget_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
uint8_t v_simplifyTarget_boxed_3757_; lean_object* v_res_3758_; 
v_simplifyTarget_boxed_3757_ = lean_unbox(v_simplifyTarget_3747_);
v_res_3758_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3744_, v_simprocs_3745_, v_fvarIdsToSimp_3746_, v_simplifyTarget_boxed_3757_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3759_, lean_object* v_simprocs_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3762_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = l_Lean_MVarId_getNondepPropHyps(v_a_3771_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___x_3774_ = 1;
v___x_3775_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3759_, v_simprocs_3760_, v_a_3773_, v___x_3774_, v___y_3762_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3775_;
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec_ref(v_simprocs_3760_);
lean_dec_ref(v_ctx_3759_);
v_a_3776_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3772_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3772_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v_simprocs_3760_);
lean_dec_ref(v_ctx_3759_);
v_a_3784_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3770_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3770_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3792_, lean_object* v_simprocs_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3792_, v_simprocs_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3804_, lean_object* v_ctx_3805_, lean_object* v_simprocs_3806_, uint8_t v_type_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3804_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3805_, v_simprocs_3806_, v_a_3818_, v_type_3807_, v___y_3809_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3819_;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_simprocs_3806_);
lean_dec_ref(v_ctx_3805_);
v_a_3820_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3817_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3817_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3828_, lean_object* v_ctx_3829_, lean_object* v_simprocs_3830_, lean_object* v_type_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v_type_555__boxed_3841_; lean_object* v_res_3842_; 
v_type_555__boxed_3841_ = lean_unbox(v_type_3831_);
v_res_3842_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3828_, v_ctx_3829_, v_simprocs_3830_, v_type_555__boxed_3841_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3843_, lean_object* v_simprocs_3844_, lean_object* v_loc_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
if (lean_obj_tag(v_loc_3845_) == 0)
{
lean_object* v___f_3855_; lean_object* v___x_3856_; 
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3855_, 0, v_ctx_3843_);
lean_closure_set(v___f_3855_, 1, v_simprocs_3844_);
v___x_3856_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3855_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
return v___x_3856_;
}
else
{
lean_object* v_hypotheses_3857_; uint8_t v_type_3858_; lean_object* v___x_3859_; lean_object* v___f_3860_; lean_object* v___x_3861_; 
v_hypotheses_3857_ = lean_ctor_get(v_loc_3845_, 0);
lean_inc_ref(v_hypotheses_3857_);
v_type_3858_ = lean_ctor_get_uint8(v_loc_3845_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3845_, 1);
v___x_3859_ = lean_box(v_type_3858_);
v___f_3860_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3860_, 0, v_hypotheses_3857_);
lean_closure_set(v___f_3860_, 1, v_ctx_3843_);
lean_closure_set(v___f_3860_, 2, v_simprocs_3844_);
lean_closure_set(v___f_3860_, 3, v___x_3859_);
v___x_3861_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3860_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
return v___x_3861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3862_, lean_object* v_simprocs_3863_, lean_object* v_loc_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3862_, v_simprocs_3863_, v_loc_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3879_, lean_object* v_stx_3880_, uint8_t v___x_3881_, lean_object* v___x_3882_, lean_object* v___x_3883_, lean_object* v___x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
if (v___x_3879_ == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_3894_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3894_;
}
else
{
lean_object* v___x_3895_; lean_object* v_tk_3896_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v___y_3984_; lean_object* v_stx_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; uint8_t v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; uint8_t v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; uint8_t v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; uint8_t v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; uint8_t v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; uint8_t v___y_4201_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; uint8_t v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v_args_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___x_4277_; uint8_t v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v_o_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v_bang_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_3895_ = lean_unsigned_to_nat(0u);
v_tk_3896_ = l_Lean_Syntax_getArg(v_stx_3880_, v___x_3895_);
v___x_4277_ = lean_unsigned_to_nat(1u);
v___x_4334_ = l_Lean_Syntax_getArg(v_stx_3880_, v___x_4277_);
v___x_4335_ = l_Lean_Syntax_isNone(v___x_4334_);
if (v___x_4335_ == 0)
{
uint8_t v___x_4336_; 
lean_inc(v___x_4334_);
v___x_4336_ = l_Lean_Syntax_matchesNull(v___x_4334_, v___x_4277_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; 
lean_dec(v___x_4334_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4337_;
}
else
{
lean_object* v_bang_4338_; lean_object* v___x_4339_; 
v_bang_4338_ = l_Lean_Syntax_getArg(v___x_4334_, v___x_3895_);
lean_dec(v___x_4334_);
v___x_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4339_, 0, v_bang_4338_);
v_bang_4307_ = v___x_4339_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
v___y_4313_ = v___y_3890_;
v___y_4314_ = v___y_3891_;
v___y_4315_ = v___y_3892_;
goto v___jp_4306_;
}
}
else
{
lean_object* v___x_4340_; 
lean_dec(v___x_4334_);
v___x_4340_ = lean_box(0);
v_bang_4307_ = v___x_4340_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
v___y_4313_ = v___y_3890_;
v___y_4314_ = v___y_3891_;
v___y_4315_ = v___y_3892_;
goto v___jp_4306_;
}
v___jp_3897_:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3899_, v___y_3902_, v___y_3909_, v___y_3901_, v___y_3908_, v___y_3905_, v___y_3903_, v___y_3900_, v___y_3904_, v___y_3898_, v___y_3907_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v_usedTheorems_3912_; lean_object* v_diag_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3955_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v_usedTheorems_3912_ = lean_ctor_get(v_a_3911_, 0);
v_diag_3913_ = lean_ctor_get(v_a_3911_, 1);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3915_ = v_a_3911_;
v_isShared_3916_ = v_isSharedCheck_3955_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_diag_3913_);
lean_inc(v_usedTheorems_3912_);
lean_dec(v_a_3911_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3955_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3906_, v_usedTheorems_3912_, v___y_3900_, v___y_3904_, v___y_3898_, v___y_3907_);
lean_dec_ref(v_usedTheorems_3912_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v_ref_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v_ref_3919_ = lean_ctor_get(v___y_3898_, 2);
v___x_3920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 1, v_a_3918_);
lean_ctor_set(v___x_3915_, 0, v___x_3920_);
v___x_3922_ = v___x_3915_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_a_3918_);
v___x_3922_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
lean_ctor_set(v___x_3924_, 2, v___x_3923_);
lean_ctor_set(v___x_3924_, 3, v___x_3923_);
lean_ctor_set(v___x_3924_, 4, v___x_3923_);
lean_ctor_set(v___x_3924_, 5, v___x_3923_);
lean_inc(v_ref_3919_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v_ref_3919_);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3927_ = 4;
v___x_3928_ = l_Lean_MessageData_nil;
v___x_3929_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3896_, v___x_3924_, v___x_3925_, v___x_3926_, v___x_3923_, v___x_3927_, v___x_3928_, v___y_3898_, v___y_3907_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v___x_3929_, 0);
lean_dec(v_unused_3937_);
v___x_3931_ = v___x_3929_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_dec(v___x_3929_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_diag_3913_);
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_diag_3913_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v_diag_3913_);
v_a_3938_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3929_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3929_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_del_object(v___x_3915_);
lean_dec_ref(v_diag_3913_);
lean_dec(v_tk_3896_);
v_a_3947_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3917_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3917_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v___y_3906_);
lean_dec(v_tk_3896_);
v_a_3956_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3910_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3910_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
v___jp_3964_:
{
if (lean_obj_tag(v___y_3965_) == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3978_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set_uint8(v___x_3978_, sizeof(void*)*1, v___x_3881_);
v___y_3898_ = v___y_3966_;
v___y_3899_ = v___y_3976_;
v___y_3900_ = v___y_3968_;
v___y_3901_ = v___y_3967_;
v___y_3902_ = v___y_3969_;
v___y_3903_ = v___y_3970_;
v___y_3904_ = v___y_3972_;
v___y_3905_ = v___y_3971_;
v___y_3906_ = v___y_3973_;
v___y_3907_ = v___y_3975_;
v___y_3908_ = v___y_3974_;
v___y_3909_ = v___x_3978_;
goto v___jp_3897_;
}
else
{
lean_object* v_val_3979_; lean_object* v___x_3980_; 
v_val_3979_ = lean_ctor_get(v___y_3965_, 0);
lean_inc(v_val_3979_);
lean_dec_ref_known(v___y_3965_, 1);
v___x_3980_ = l_Lean_Elab_Tactic_expandLocation(v_val_3979_);
lean_dec(v_val_3979_);
v___y_3898_ = v___y_3966_;
v___y_3899_ = v___y_3976_;
v___y_3900_ = v___y_3968_;
v___y_3901_ = v___y_3967_;
v___y_3902_ = v___y_3969_;
v___y_3903_ = v___y_3970_;
v___y_3904_ = v___y_3972_;
v___y_3905_ = v___y_3971_;
v___y_3906_ = v___y_3973_;
v___y_3907_ = v___y_3975_;
v___y_3908_ = v___y_3974_;
v___y_3909_ = v___x_3980_;
goto v___jp_3897_;
}
}
v___jp_3981_:
{
uint8_t v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3994_ = 0;
v___x_3995_ = 2;
v___x_3996_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3997_ = lean_box(v___x_3994_);
v___x_3998_ = lean_box(v___x_3995_);
v___x_3999_ = lean_box(v___x_3994_);
lean_inc(v_stx_3985_);
v___x_4000_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4000_, 0, v_stx_3985_);
lean_closure_set(v___x_4000_, 1, v___x_3997_);
lean_closure_set(v___x_4000_, 2, v___x_3998_);
lean_closure_set(v___x_4000_, 3, v___x_3999_);
lean_closure_set(v___x_4000_, 4, v___x_3996_);
v___x_4001_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4000_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
if (lean_obj_tag(v___y_3984_) == 0)
{
lean_object* v_ctx_4003_; lean_object* v_simprocs_4004_; 
v_ctx_4003_ = lean_ctor_get(v_a_4002_, 0);
lean_inc_ref(v_ctx_4003_);
v_simprocs_4004_ = lean_ctor_get(v_a_4002_, 1);
lean_inc_ref(v_simprocs_4004_);
lean_dec(v_a_4002_);
v___y_3965_ = v___y_3982_;
v___y_3966_ = v___y_3992_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3990_;
v___y_3969_ = v_simprocs_4004_;
v___y_3970_ = v___y_3989_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___y_3991_;
v___y_3973_ = v_stx_3985_;
v___y_3974_ = v___y_3987_;
v___y_3975_ = v___y_3993_;
v___y_3976_ = v_ctx_4003_;
goto v___jp_3964_;
}
else
{
lean_dec_ref_known(v___y_3984_, 1);
if (v___y_3983_ == 0)
{
lean_object* v_ctx_4005_; lean_object* v_simprocs_4006_; 
v_ctx_4005_ = lean_ctor_get(v_a_4002_, 0);
lean_inc_ref(v_ctx_4005_);
v_simprocs_4006_ = lean_ctor_get(v_a_4002_, 1);
lean_inc_ref(v_simprocs_4006_);
lean_dec(v_a_4002_);
v___y_3965_ = v___y_3982_;
v___y_3966_ = v___y_3992_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3990_;
v___y_3969_ = v_simprocs_4006_;
v___y_3970_ = v___y_3989_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___y_3991_;
v___y_3973_ = v_stx_3985_;
v___y_3974_ = v___y_3987_;
v___y_3975_ = v___y_3993_;
v___y_3976_ = v_ctx_4005_;
goto v___jp_3964_;
}
else
{
lean_object* v_ctx_4007_; lean_object* v_simprocs_4008_; lean_object* v___x_4009_; 
v_ctx_4007_ = lean_ctor_get(v_a_4002_, 0);
lean_inc_ref(v_ctx_4007_);
v_simprocs_4008_ = lean_ctor_get(v_a_4002_, 1);
lean_inc_ref(v_simprocs_4008_);
lean_dec(v_a_4002_);
v___x_4009_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4007_);
v___y_3965_ = v___y_3982_;
v___y_3966_ = v___y_3992_;
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3990_;
v___y_3969_ = v_simprocs_4008_;
v___y_3970_ = v___y_3989_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___y_3991_;
v___y_3973_ = v_stx_3985_;
v___y_3974_ = v___y_3987_;
v___y_3975_ = v___y_3993_;
v___y_3976_ = v___x_4009_;
goto v___jp_3964_;
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_stx_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3982_);
lean_dec(v_tk_3896_);
v_a_4010_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4001_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4001_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
v___jp_4018_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_inc_ref(v___y_4020_);
v___x_4040_ = l_Array_append___redArg(v___y_4020_, v___y_4039_);
lean_dec_ref(v___y_4039_);
lean_inc(v___y_4026_);
lean_inc(v___y_4019_);
v___x_4041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4041_, 0, v___y_4019_);
lean_ctor_set(v___x_4041_, 1, v___y_4026_);
lean_ctor_set(v___x_4041_, 2, v___x_4040_);
v___x_4042_ = l_Lean_Syntax_node6(v___y_4019_, v___y_4022_, v___y_4036_, v___y_4025_, v___y_4031_, v___y_4027_, v___y_4033_, v___x_4041_);
v___y_3982_ = v___y_4032_;
v___y_3983_ = v___y_4035_;
v___y_3984_ = v___y_4024_;
v_stx_3985_ = v___x_4042_;
v___y_3986_ = v___y_4023_;
v___y_3987_ = v___y_4021_;
v___y_3988_ = v___y_4037_;
v___y_3989_ = v___y_4038_;
v___y_3990_ = v___y_4034_;
v___y_3991_ = v___y_4030_;
v___y_3992_ = v___y_4029_;
v___y_3993_ = v___y_4028_;
goto v___jp_3981_;
}
v___jp_4043_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_inc_ref(v___y_4045_);
v___x_4064_ = l_Array_append___redArg(v___y_4045_, v___y_4063_);
lean_dec_ref(v___y_4063_);
lean_inc(v___y_4051_);
lean_inc(v___y_4044_);
v___x_4065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___y_4044_);
lean_ctor_set(v___x_4065_, 1, v___y_4051_);
lean_ctor_set(v___x_4065_, 2, v___x_4064_);
if (lean_obj_tag(v___y_4057_) == 0)
{
lean_object* v___x_4066_; 
v___x_4066_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4046_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4049_;
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___x_4065_;
v___y_4034_ = v___y_4058_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4060_;
v___y_4038_ = v___y_4062_;
v___y_4039_ = v___x_4066_;
goto v___jp_4018_;
}
else
{
lean_object* v_val_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_val_4067_ = lean_ctor_get(v___y_4057_, 0);
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4067_);
v___x_4069_ = lean_array_push(v___x_4068_, v_val_4067_);
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4046_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4049_;
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___x_4065_;
v___y_4034_ = v___y_4058_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4060_;
v___y_4038_ = v___y_4062_;
v___y_4039_ = v___x_4069_;
goto v___jp_4018_;
}
}
v___jp_4070_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_inc_ref(v___y_4072_);
v___x_4091_ = l_Array_append___redArg(v___y_4072_, v___y_4090_);
lean_dec_ref(v___y_4090_);
lean_inc(v___y_4078_);
lean_inc(v___y_4071_);
v___x_4092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4092_, 0, v___y_4071_);
lean_ctor_set(v___x_4092_, 1, v___y_4078_);
lean_ctor_set(v___x_4092_, 2, v___x_4091_);
if (lean_obj_tag(v___y_4089_) == 1)
{
lean_object* v_val_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_val_4093_ = lean_ctor_get(v___y_4089_, 0);
lean_inc(v_val_4093_);
lean_dec_ref_known(v___y_4089_, 1);
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4071_, 3);
v___x_4095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___y_4071_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
lean_inc_ref(v___y_4072_);
v___x_4096_ = l_Array_append___redArg(v___y_4072_, v_val_4093_);
lean_dec(v_val_4093_);
lean_inc(v___y_4078_);
v___x_4097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4097_, 0, v___y_4071_);
lean_ctor_set(v___x_4097_, 1, v___y_4078_);
lean_ctor_set(v___x_4097_, 2, v___x_4096_);
v___x_4098_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4071_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Array_mkArray3___redArg(v___x_4095_, v___x_4097_, v___x_4099_);
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4072_;
v___y_4046_ = v___y_4073_;
v___y_4047_ = v___y_4074_;
v___y_4048_ = v___y_4075_;
v___y_4049_ = v___y_4076_;
v___y_4050_ = v___y_4077_;
v___y_4051_ = v___y_4078_;
v___y_4052_ = v___x_4092_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___x_4100_;
goto v___jp_4043_;
}
else
{
lean_object* v___x_4101_; 
lean_dec(v___y_4089_);
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4072_;
v___y_4046_ = v___y_4073_;
v___y_4047_ = v___y_4074_;
v___y_4048_ = v___y_4075_;
v___y_4049_ = v___y_4076_;
v___y_4050_ = v___y_4077_;
v___y_4051_ = v___y_4078_;
v___y_4052_ = v___x_4092_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___x_4101_;
goto v___jp_4043_;
}
}
v___jp_4102_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_inc_ref(v___y_4122_);
v___x_4124_ = l_Array_append___redArg(v___y_4122_, v___y_4123_);
lean_dec_ref(v___y_4123_);
lean_inc(v___y_4117_);
lean_inc(v___y_4112_);
v___x_4125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4125_, 0, v___y_4112_);
lean_ctor_set(v___x_4125_, 1, v___y_4117_);
lean_ctor_set(v___x_4125_, 2, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node6(v___y_4112_, v___y_4113_, v___y_4104_, v___y_4107_, v___y_4110_, v___y_4119_, v___y_4120_, v___x_4125_);
v___y_3982_ = v___y_4114_;
v___y_3983_ = v___y_4116_;
v___y_3984_ = v___y_4106_;
v_stx_3985_ = v___x_4126_;
v___y_3986_ = v___y_4105_;
v___y_3987_ = v___y_4103_;
v___y_3988_ = v___y_4118_;
v___y_3989_ = v___y_4121_;
v___y_3990_ = v___y_4115_;
v___y_3991_ = v___y_4111_;
v___y_3992_ = v___y_4109_;
v___y_3993_ = v___y_4108_;
goto v___jp_3981_;
}
v___jp_4127_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_inc_ref(v___y_4146_);
v___x_4148_ = l_Array_append___redArg(v___y_4146_, v___y_4147_);
lean_dec_ref(v___y_4147_);
lean_inc(v___y_4143_);
lean_inc(v___y_4136_);
v___x_4149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4149_, 0, v___y_4136_);
lean_ctor_set(v___x_4149_, 1, v___y_4143_);
lean_ctor_set(v___x_4149_, 2, v___x_4148_);
if (lean_obj_tag(v___y_4139_) == 0)
{
lean_object* v___x_4150_; 
v___x_4150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4130_;
v___y_4106_ = v___y_4131_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4145_;
v___y_4120_ = v___x_4149_;
v___y_4121_ = v___y_4144_;
v___y_4122_ = v___y_4146_;
v___y_4123_ = v___x_4150_;
goto v___jp_4102_;
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_val_4151_ = lean_ctor_get(v___y_4139_, 0);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4151_);
v___x_4153_ = lean_array_push(v___x_4152_, v_val_4151_);
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4130_;
v___y_4106_ = v___y_4131_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4145_;
v___y_4120_ = v___x_4149_;
v___y_4121_ = v___y_4144_;
v___y_4122_ = v___y_4146_;
v___y_4123_ = v___x_4153_;
goto v___jp_4102_;
}
}
v___jp_4154_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_inc_ref(v___y_4172_);
v___x_4175_ = l_Array_append___redArg(v___y_4172_, v___y_4174_);
lean_dec_ref(v___y_4174_);
lean_inc(v___y_4170_);
lean_inc(v___y_4163_);
v___x_4176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4176_, 0, v___y_4163_);
lean_ctor_set(v___x_4176_, 1, v___y_4170_);
lean_ctor_set(v___x_4176_, 2, v___x_4175_);
if (lean_obj_tag(v___y_4173_) == 1)
{
lean_object* v_val_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_val_4177_ = lean_ctor_get(v___y_4173_, 0);
lean_inc(v_val_4177_);
lean_dec_ref_known(v___y_4173_, 1);
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4163_, 3);
v___x_4179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___y_4163_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
lean_inc_ref(v___y_4172_);
v___x_4180_ = l_Array_append___redArg(v___y_4172_, v_val_4177_);
lean_dec(v_val_4177_);
lean_inc(v___y_4170_);
v___x_4181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4181_, 0, v___y_4163_);
lean_ctor_set(v___x_4181_, 1, v___y_4170_);
lean_ctor_set(v___x_4181_, 2, v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___y_4163_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v___x_4184_ = l_Array_mkArray3___redArg(v___x_4179_, v___x_4181_, v___x_4183_);
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4166_;
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___x_4176_;
v___y_4146_ = v___y_4172_;
v___y_4147_ = v___x_4184_;
goto v___jp_4127_;
}
else
{
lean_object* v___x_4185_; 
lean_dec(v___y_4173_);
v___x_4185_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4166_;
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___x_4176_;
v___y_4146_ = v___y_4172_;
v___y_4147_ = v___x_4185_;
goto v___jp_4127_;
}
}
v___jp_4186_:
{
lean_object* v_ref_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_ref_4202_ = lean_ctor_get(v___y_4191_, 2);
v___x_4203_ = l_Lean_SourceInfo_fromRef(v_ref_4202_, v___y_4201_);
v___x_4204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4205_ = l_Lean_Name_mkStr4(v___x_3882_, v___x_3883_, v___x_3884_, v___x_4204_);
v___x_4206_ = l_Lean_SourceInfo_fromRef(v_tk_3896_, v___x_3881_);
v___x_4207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
lean_ctor_set(v___x_4207_, 1, v___x_4204_);
v___x_4208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4209_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4203_);
v___x_4210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4203_);
lean_ctor_set(v___x_4210_, 1, v___x_4208_);
lean_ctor_set(v___x_4210_, 2, v___x_4209_);
if (lean_obj_tag(v___y_4198_) == 1)
{
lean_object* v_val_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_val_4211_ = lean_ctor_get(v___y_4198_, 0);
lean_inc(v_val_4211_);
lean_dec_ref_known(v___y_4198_, 1);
v___x_4212_ = l_Lean_SourceInfo_fromRef(v_val_4211_, v___x_3881_);
lean_dec(v_val_4211_);
v___x_4213_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4212_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l_Array_mkArray1___redArg(v___x_4214_);
v___y_4071_ = v___x_4203_;
v___y_4072_ = v___x_4209_;
v___y_4073_ = v___y_4187_;
v___y_4074_ = v___x_4205_;
v___y_4075_ = v___y_4188_;
v___y_4076_ = v___y_4189_;
v___y_4077_ = v___y_4190_;
v___y_4078_ = v___x_4208_;
v___y_4079_ = v___y_4192_;
v___y_4080_ = v___y_4191_;
v___y_4081_ = v___y_4193_;
v___y_4082_ = v___x_4210_;
v___y_4083_ = v___y_4194_;
v___y_4084_ = v___y_4195_;
v___y_4085_ = v___y_4196_;
v___y_4086_ = v___x_4207_;
v___y_4087_ = v___y_4197_;
v___y_4088_ = v___y_4199_;
v___y_4089_ = v___y_4200_;
v___y_4090_ = v___x_4215_;
goto v___jp_4070_;
}
else
{
lean_object* v___x_4216_; 
lean_dec(v___y_4198_);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4071_ = v___x_4203_;
v___y_4072_ = v___x_4209_;
v___y_4073_ = v___y_4187_;
v___y_4074_ = v___x_4205_;
v___y_4075_ = v___y_4188_;
v___y_4076_ = v___y_4189_;
v___y_4077_ = v___y_4190_;
v___y_4078_ = v___x_4208_;
v___y_4079_ = v___y_4192_;
v___y_4080_ = v___y_4191_;
v___y_4081_ = v___y_4193_;
v___y_4082_ = v___x_4210_;
v___y_4083_ = v___y_4194_;
v___y_4084_ = v___y_4195_;
v___y_4085_ = v___y_4196_;
v___y_4086_ = v___x_4207_;
v___y_4087_ = v___y_4197_;
v___y_4088_ = v___y_4199_;
v___y_4089_ = v___y_4200_;
v___y_4090_ = v___x_4216_;
goto v___jp_4070_;
}
}
v___jp_4217_:
{
if (lean_obj_tag(v___y_4220_) == 0)
{
uint8_t v___x_4232_; 
v___x_4232_ = 0;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4231_;
v___y_4195_ = v___y_4225_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4227_;
v___y_4198_ = v___y_4228_;
v___y_4199_ = v___y_4229_;
v___y_4200_ = v___y_4230_;
v___y_4201_ = v___x_4232_;
goto v___jp_4186_;
}
else
{
if (v___y_4226_ == 0)
{
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4231_;
v___y_4195_ = v___y_4225_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4227_;
v___y_4198_ = v___y_4228_;
v___y_4199_ = v___y_4229_;
v___y_4200_ = v___y_4230_;
v___y_4201_ = v___y_4226_;
goto v___jp_4186_;
}
else
{
lean_object* v_ref_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v_ref_4233_ = lean_ctor_get(v___y_4222_, 2);
v___x_4234_ = 0;
v___x_4235_ = l_Lean_SourceInfo_fromRef(v_ref_4233_, v___x_4234_);
v___x_4236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4237_ = l_Lean_Name_mkStr4(v___x_3882_, v___x_3883_, v___x_3884_, v___x_4236_);
v___x_4238_ = l_Lean_SourceInfo_fromRef(v_tk_3896_, v___x_3881_);
v___x_4239_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4238_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4242_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4235_);
v___x_4243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4235_);
lean_ctor_set(v___x_4243_, 1, v___x_4241_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
if (lean_obj_tag(v___y_4228_) == 1)
{
lean_object* v_val_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_val_4244_ = lean_ctor_get(v___y_4228_, 0);
lean_inc(v_val_4244_);
lean_dec_ref_known(v___y_4228_, 1);
v___x_4245_ = l_Lean_SourceInfo_fromRef(v_val_4244_, v___x_3881_);
lean_dec(v_val_4244_);
v___x_4246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l_Array_mkArray1___redArg(v___x_4247_);
v___y_4155_ = v___y_4218_;
v___y_4156_ = v___x_4240_;
v___y_4157_ = v___y_4219_;
v___y_4158_ = v___y_4220_;
v___y_4159_ = v___y_4221_;
v___y_4160_ = v___y_4223_;
v___y_4161_ = v___y_4222_;
v___y_4162_ = v___x_4243_;
v___y_4163_ = v___x_4235_;
v___y_4164_ = v___y_4224_;
v___y_4165_ = v___x_4237_;
v___y_4166_ = v___y_4231_;
v___y_4167_ = v___y_4225_;
v___y_4168_ = v___y_4226_;
v___y_4169_ = v___y_4227_;
v___y_4170_ = v___x_4241_;
v___y_4171_ = v___y_4229_;
v___y_4172_ = v___x_4242_;
v___y_4173_ = v___y_4230_;
v___y_4174_ = v___x_4248_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4249_; 
lean_dec(v___y_4228_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4155_ = v___y_4218_;
v___y_4156_ = v___x_4240_;
v___y_4157_ = v___y_4219_;
v___y_4158_ = v___y_4220_;
v___y_4159_ = v___y_4221_;
v___y_4160_ = v___y_4223_;
v___y_4161_ = v___y_4222_;
v___y_4162_ = v___x_4243_;
v___y_4163_ = v___x_4235_;
v___y_4164_ = v___y_4224_;
v___y_4165_ = v___x_4237_;
v___y_4166_ = v___y_4231_;
v___y_4167_ = v___y_4225_;
v___y_4168_ = v___y_4226_;
v___y_4169_ = v___y_4227_;
v___y_4170_ = v___x_4241_;
v___y_4171_ = v___y_4229_;
v___y_4172_ = v___x_4242_;
v___y_4173_ = v___y_4230_;
v___y_4174_ = v___x_4249_;
goto v___jp_4154_;
}
}
}
}
v___jp_4250_:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4265_ = lean_unsigned_to_nat(3u);
v___x_4266_ = l_Lean_Syntax_getArg(v___y_4255_, v___x_4265_);
lean_dec(v___y_4255_);
v___x_4267_ = l_Lean_Syntax_getOptional_x3f(v___x_4266_);
lean_dec(v___x_4266_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_box(0);
v___y_4218_ = v___y_4258_;
v___y_4219_ = v___y_4257_;
v___y_4220_ = v___y_4254_;
v___y_4221_ = v___y_4253_;
v___y_4222_ = v___y_4263_;
v___y_4223_ = v___y_4264_;
v___y_4224_ = v___y_4262_;
v___y_4225_ = v___y_4261_;
v___y_4226_ = v___y_4251_;
v___y_4227_ = v___y_4259_;
v___y_4228_ = v___y_4252_;
v___y_4229_ = v___y_4260_;
v___y_4230_ = v_args_4256_;
v___y_4231_ = v___x_4268_;
goto v___jp_4217_;
}
else
{
lean_object* v_val_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
v_val_4269_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4267_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_val_4269_);
lean_dec(v___x_4267_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_val_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
v___y_4218_ = v___y_4258_;
v___y_4219_ = v___y_4257_;
v___y_4220_ = v___y_4254_;
v___y_4221_ = v___y_4253_;
v___y_4222_ = v___y_4263_;
v___y_4223_ = v___y_4264_;
v___y_4224_ = v___y_4262_;
v___y_4225_ = v___y_4261_;
v___y_4226_ = v___y_4251_;
v___y_4227_ = v___y_4259_;
v___y_4228_ = v___y_4252_;
v___y_4229_ = v___y_4260_;
v___y_4230_ = v_args_4256_;
v___y_4231_ = v___x_4274_;
goto v___jp_4217_;
}
}
}
}
v___jp_4278_:
{
lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4293_ = l_Lean_Syntax_getArg(v___y_4283_, v___y_4280_);
v___x_4294_ = l_Lean_Syntax_isNone(v___x_4293_);
if (v___x_4294_ == 0)
{
uint8_t v___x_4295_; 
lean_inc(v___x_4293_);
v___x_4295_ = l_Lean_Syntax_matchesNull(v___x_4293_, v___x_4277_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; 
lean_dec(v___x_4293_);
lean_dec(v_o_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4296_;
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4297_ = l_Lean_Syntax_getArg(v___x_4293_, v___x_3895_);
lean_dec(v___x_4293_);
v___x_4298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3884_);
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
v___x_4299_ = l_Lean_Name_mkStr4(v___x_3882_, v___x_3883_, v___x_3884_, v___x_4298_);
lean_inc(v___x_4297_);
v___x_4300_ = l_Lean_Syntax_isOfKind(v___x_4297_, v___x_4299_);
lean_dec(v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
lean_dec(v___x_4297_);
lean_dec(v_o_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; lean_object* v_args_4303_; lean_object* v___x_4304_; 
v___x_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4277_);
lean_dec(v___x_4297_);
v_args_4303_ = l_Lean_Syntax_getArgs(v___x_4302_);
lean_dec(v___x_4302_);
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_args_4303_);
v___y_4251_ = v___y_4279_;
v___y_4252_ = v_o_4284_;
v___y_4253_ = v___y_4282_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v___y_4283_;
v_args_4256_ = v___x_4304_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v___y_4262_ = v___y_4290_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
goto v___jp_4250_;
}
}
}
else
{
lean_object* v___x_4305_; 
lean_dec(v___x_4293_);
v___x_4305_ = lean_box(0);
v___y_4251_ = v___y_4279_;
v___y_4252_ = v_o_4284_;
v___y_4253_ = v___y_4282_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v___y_4283_;
v_args_4256_ = v___x_4305_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v___y_4262_ = v___y_4290_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
goto v___jp_4250_;
}
}
v___jp_4306_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4316_ = lean_unsigned_to_nat(2u);
v___x_4317_ = l_Lean_Syntax_getArg(v_stx_3880_, v___x_4316_);
v___x_4318_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3884_);
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
v___x_4319_ = l_Lean_Name_mkStr4(v___x_3882_, v___x_3883_, v___x_3884_, v___x_4318_);
lean_inc(v___x_4317_);
v___x_4320_ = l_Lean_Syntax_isOfKind(v___x_4317_, v___x_4319_);
lean_dec(v___x_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; 
lean_dec(v___x_4317_);
lean_dec(v_bang_4307_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4321_;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4322_ = l_Lean_Syntax_getArg(v___x_4317_, v___x_3895_);
v___x_4323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3884_);
lean_inc_ref(v___x_3883_);
lean_inc_ref(v___x_3882_);
v___x_4324_ = l_Lean_Name_mkStr4(v___x_3882_, v___x_3883_, v___x_3884_, v___x_4323_);
lean_inc(v___x_4322_);
v___x_4325_ = l_Lean_Syntax_isOfKind(v___x_4322_, v___x_4324_);
lean_dec(v___x_4324_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; 
lean_dec(v___x_4322_);
lean_dec(v___x_4317_);
lean_dec(v_bang_4307_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4326_;
}
else
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = l_Lean_Syntax_getArg(v___x_4317_, v___x_4277_);
v___x_4328_ = l_Lean_Syntax_isNone(v___x_4327_);
if (v___x_4328_ == 0)
{
uint8_t v___x_4329_; 
lean_inc(v___x_4327_);
v___x_4329_ = l_Lean_Syntax_matchesNull(v___x_4327_, v___x_4277_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
lean_dec(v___x_4327_);
lean_dec(v___x_4322_);
lean_dec(v___x_4317_);
lean_dec(v_bang_4307_);
lean_dec(v_tk_3896_);
lean_dec_ref(v___x_3884_);
lean_dec_ref(v___x_3883_);
lean_dec_ref(v___x_3882_);
v___x_4330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4330_;
}
else
{
lean_object* v_o_4331_; lean_object* v___x_4332_; 
v_o_4331_ = l_Lean_Syntax_getArg(v___x_4327_, v___x_3895_);
lean_dec(v___x_4327_);
v___x_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4332_, 0, v_o_4331_);
v___y_4279_ = v___x_4320_;
v___y_4280_ = v___x_4316_;
v___y_4281_ = v_bang_4307_;
v___y_4282_ = v___x_4322_;
v___y_4283_ = v___x_4317_;
v_o_4284_ = v___x_4332_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
v___y_4290_ = v___y_4313_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4315_;
goto v___jp_4278_;
}
}
else
{
lean_object* v___x_4333_; 
lean_dec(v___x_4327_);
v___x_4333_ = lean_box(0);
v___y_4279_ = v___x_4320_;
v___y_4280_ = v___x_4316_;
v___y_4281_ = v_bang_4307_;
v___y_4282_ = v___x_4322_;
v___y_4283_ = v___x_4317_;
v_o_4284_ = v___x_4333_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
v___y_4290_ = v___y_4313_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4315_;
goto v___jp_4278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4341_, lean_object* v_stx_4342_, lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v___x_4345_, lean_object* v___x_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
uint8_t v___x_8035__boxed_4356_; uint8_t v___x_8036__boxed_4357_; lean_object* v_res_4358_; 
v___x_8035__boxed_4356_ = lean_unbox(v___x_4341_);
v___x_8036__boxed_4357_ = lean_unbox(v___x_4343_);
v_res_4358_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8035__boxed_4356_, v_stx_4342_, v___x_8036__boxed_4357_, v___x_4344_, v___x_4345_, v___x_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v_stx_4342_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; uint8_t v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___y_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4378_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4365_);
v___x_4379_ = l_Lean_Syntax_isOfKind(v_stx_4365_, v___x_4378_);
v___x_4380_ = 1;
v___x_4381_ = lean_box(v___x_4379_);
v___x_4382_ = lean_box(v___x_4380_);
v___y_4383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4383_, 0, v___x_4381_);
lean_closure_set(v___y_4383_, 1, v_stx_4365_);
lean_closure_set(v___y_4383_, 2, v___x_4382_);
lean_closure_set(v___y_4383_, 3, v___x_4375_);
lean_closure_set(v___y_4383_, 4, v___x_4376_);
lean_closure_set(v___y_4383_, 5, v___x_4377_);
v___x_4384_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4384_, 0, v___y_4383_);
v___x_4385_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4384_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4404_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4408_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4404_, v___x_4405_, v___x_4406_, v___x_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4439_ = l_Lean_addBuiltinDeclarationRanges(v___x_4437_, v___x_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4441_;
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
