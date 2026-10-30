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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_dec(v_pre_28_);
lean_dec_ref_known(v_pre_27_, 2);
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
lean_dec(v_pre_27_);
lean_dec_ref_known(v_pre_26_, 2);
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
size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_102_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_105_, v___x_106_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_107_;
goto v___jp_96_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_111_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_125_, lean_object* v_usedSimps_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_stx_132_; lean_object* v___x_133_; 
v_stx_132_ = l_Lean_Syntax_unsetTrailing(v_stx_125_);
v___x_133_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_132_, v_usedSimps_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_133_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_133_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_150_, lean_object* v_usedSimps_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_150_, v_usedSimps_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec_ref(v_usedSimps_151_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v___x_159_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(v___x_188_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
uint8_t v___x_33496__boxed_204_; lean_object* v_res_205_; 
v___x_33496__boxed_204_ = lean_unbox(v___x_197_);
v_res_205_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33496__boxed_204_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v_x_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_206_, lean_object* v___x_207_, uint8_t v___x_208_, lean_object* v___y_209_, lean_object* v_simprocs_210_, lean_object* v_discharge_x3f_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
if (lean_obj_tag(v___y_206_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_207_);
v___x_222_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_208_);
v___x_223_ = l_Lean_Elab_Tactic_simpLocation(v___y_209_, v_simprocs_210_, v_discharge_x3f_211_, v___x_222_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_val_224_ = lean_ctor_get(v___y_206_, 0);
v___x_225_ = l_Lean_Elab_Tactic_expandLocation(v_val_224_);
v___x_226_ = l_Lean_Elab_Tactic_simpLocation(v___y_209_, v_simprocs_210_, v_discharge_x3f_211_, v___x_225_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v___y_230_, lean_object* v_simprocs_231_, lean_object* v_discharge_x3f_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v___x_33523__boxed_242_; lean_object* v_res_243_; 
v___x_33523__boxed_242_ = lean_unbox(v___x_229_);
v_res_243_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_227_, v___x_228_, v___x_33523__boxed_242_, v___y_230_, v_simprocs_231_, v_discharge_x3f_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_228_);
lean_dec(v___y_227_);
return v_res_243_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Array_mkArray0___redArg();
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_254_, lean_object* v_as_x27_255_, lean_object* v_b_256_, lean_object* v___y_257_){
_start:
{
if (lean_obj_tag(v_as_x27_255_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_b_256_);
return v___x_259_;
}
else
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v_ref_262_; uint8_t v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_head_260_ = lean_ctor_get(v_as_x27_255_, 0);
v_tail_261_ = lean_ctor_get(v_as_x27_255_, 1);
v_ref_262_ = lean_ctor_get(v___y_257_, 2);
v___x_263_ = 1;
v___x_264_ = 0;
v___x_265_ = l_Lean_SourceInfo_fromRef(v_ref_262_, v___x_264_);
v___x_266_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_268_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_265_);
v___x_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
lean_inc(v_head_260_);
v___x_270_ = l_Lean_mkCIdentFrom(v___x_254_, v_head_260_, v___x_263_);
lean_inc_ref(v___x_269_);
v___x_271_ = l_Lean_Syntax_node3(v___x_265_, v___x_266_, v___x_269_, v___x_269_, v___x_270_);
v___x_272_ = lean_array_push(v_b_256_, v___x_271_);
v_as_x27_255_ = v_tail_261_;
v_b_256_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_274_, lean_object* v_as_x27_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_274_, v_as_x27_275_, v_b_276_, v___y_277_);
lean_dec_ref(v___y_277_);
lean_dec(v_as_x27_275_);
lean_dec(v___x_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_head_282_; lean_object* v_tail_283_; lean_object* v_fst_284_; uint8_t v___x_285_; 
v_head_282_ = lean_ctor_get(v_x_280_, 0);
v_tail_283_ = lean_ctor_get(v_x_280_, 1);
v_fst_284_ = lean_ctor_get(v_head_282_, 0);
v___x_285_ = l_Lean_isPrivateName(v_fst_284_);
if (v___x_285_ == 0)
{
v_x_280_ = v_tail_283_;
goto _start;
}
else
{
lean_object* v___x_287_; 
lean_inc(v_head_282_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_head_282_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_288_);
lean_dec(v_x_288_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_290_, lean_object* v_opt_291_){
_start:
{
lean_object* v_name_292_; lean_object* v_defValue_293_; lean_object* v_map_294_; lean_object* v___x_295_; 
v_name_292_ = lean_ctor_get(v_opt_291_, 0);
v_defValue_293_ = lean_ctor_get(v_opt_291_, 1);
v_map_294_ = lean_ctor_get(v_opts_290_, 0);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_294_, v_name_292_);
if (lean_obj_tag(v___x_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = lean_unbox(v_defValue_293_);
return v___x_296_;
}
else
{
lean_object* v_val_297_; 
v_val_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_295_, 1);
if (lean_obj_tag(v_val_297_) == 1)
{
uint8_t v_v_298_; 
v_v_298_ = lean_ctor_get_uint8(v_val_297_, 0);
lean_dec_ref_known(v_val_297_, 0);
return v_v_298_;
}
else
{
uint8_t v___x_299_; 
lean_dec(v_val_297_);
v___x_299_ = lean_unbox(v_defValue_293_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_300_, lean_object* v_opt_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_300_, v_opt_301_);
lean_dec_ref(v_opt_301_);
lean_dec_ref(v_opts_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_305_);
v___x_308_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_307_, v_opt_304_);
lean_dec_ref(v___x_307_);
v___x_309_ = lean_box(v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_311_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v_opt_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_env_322_; uint8_t v___x_323_; lean_object* v_env_324_; lean_object* v___x_325_; lean_object* v_toCold_326_; lean_object* v_mctx_327_; lean_object* v_lctx_328_; lean_object* v_options_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_321_ = lean_st_ref_get(v___y_319_);
v_env_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_env_322_);
lean_dec(v___x_321_);
v___x_323_ = 0;
v_env_324_ = l_Lean_Environment_setRecordingDeps(v_env_322_, v___x_323_);
v___x_325_ = lean_st_ref_get(v___y_317_);
v_toCold_326_ = lean_ctor_get(v___y_318_, 0);
v_mctx_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_mctx_327_);
lean_dec(v___x_325_);
v_lctx_328_ = lean_ctor_get(v___y_316_, 2);
v_options_329_ = lean_ctor_get(v_toCold_326_, 2);
lean_inc_ref(v_options_329_);
lean_inc_ref(v_lctx_328_);
v___x_330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_330_, 0, v_env_324_);
lean_ctor_set(v___x_330_, 1, v_mctx_327_);
lean_ctor_set(v___x_330_, 2, v_lctx_328_);
lean_ctor_set(v___x_330_, 3, v_options_329_);
v___x_331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_msgData_315_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 1)
{
lean_object* v_pre_349_; 
v_pre_349_ = lean_ctor_get(v_x_348_, 0);
switch(lean_obj_tag(v_pre_349_))
{
case 1:
{
lean_object* v_pre_350_; 
v_pre_350_ = lean_ctor_get(v_pre_349_, 0);
switch(lean_obj_tag(v_pre_350_))
{
case 0:
{
lean_object* v_str_351_; lean_object* v_str_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_str_351_ = lean_ctor_get(v_x_348_, 1);
v_str_352_ = lean_ctor_get(v_pre_349_, 1);
v___x_353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_354_ = lean_string_dec_eq(v_str_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_356_ = lean_string_dec_eq(v_str_352_, v___x_355_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_358_ = lean_string_dec_eq(v_str_351_, v___x_357_);
if (v___x_358_ == 0)
{
return v___x_358_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_360_ = lean_string_dec_eq(v_str_351_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_360_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
case 1:
{
lean_object* v_pre_361_; 
v_pre_361_ = lean_ctor_get(v_pre_350_, 0);
if (lean_obj_tag(v_pre_361_) == 0)
{
lean_object* v_str_362_; lean_object* v_str_363_; lean_object* v_str_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_str_362_ = lean_ctor_get(v_x_348_, 1);
v_str_363_ = lean_ctor_get(v_pre_349_, 1);
v_str_364_ = lean_ctor_get(v_pre_350_, 1);
v___x_365_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_366_ = lean_string_dec_eq(v_str_364_, v___x_365_);
if (v___x_366_ == 0)
{
return v___x_366_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_368_ = lean_string_dec_eq(v_str_363_, v___x_367_);
if (v___x_368_ == 0)
{
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_370_ = lean_string_dec_eq(v_str_362_, v___x_369_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
default: 
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
}
}
case 0:
{
lean_object* v_str_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_str_373_ = lean_ctor_get(v_x_348_, 1);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_375_ = lean_string_dec_eq(v_str_373_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_347_;
}
}
default: 
{
uint8_t v___x_376_; 
v___x_376_ = 0;
return v___x_376_;
}
}
}
else
{
uint8_t v___x_377_; 
v___x_377_ = 0;
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_suppressElabErrors_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_378_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_380_, v_x_379_);
lean_dec(v_x_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___y_394_; uint8_t v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v_toCold_401_; lean_object* v___y_402_; lean_object* v___y_431_; lean_object* v___y_432_; uint8_t v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; uint8_t v___y_463_; lean_object* v___y_464_; uint8_t v___y_468_; uint8_t v___y_469_; uint8_t v___x_479_; uint8_t v___y_481_; uint8_t v___x_487_; 
v___x_479_ = 2;
v___x_487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_479_);
if (v___x_487_ == 0)
{
v___y_481_ = v___x_487_;
goto v___jp_480_;
}
else
{
uint8_t v___x_488_; 
lean_inc_ref(v_msgData_385_);
v___x_488_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_385_);
if (v___x_488_ == 0)
{
v___y_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_msgData_385_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
v___jp_393_:
{
lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_env_409_; lean_object* v_nextMacroScope_410_; lean_object* v_ngen_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_traceState_413_; lean_object* v_cache_414_; lean_object* v_recordedDeps_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
v_currNamespace_403_ = lean_ctor_get(v_toCold_401_, 4);
v_openDecls_404_ = lean_ctor_get(v_toCold_401_, 5);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_currNamespace_403_);
lean_ctor_set(v___x_405_, 1, v_openDecls_404_);
v___x_406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___y_394_);
lean_inc_ref(v___y_398_);
lean_inc_ref(v___y_399_);
v___x_407_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_407_, 0, v___y_399_);
lean_ctor_set(v___x_407_, 1, v___y_397_);
lean_ctor_set(v___x_407_, 2, v___y_396_);
lean_ctor_set(v___x_407_, 3, v___y_398_);
lean_ctor_set(v___x_407_, 4, v___x_406_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5, v___y_400_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5 + 1, v___y_395_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5 + 2, v_isSilent_387_);
v___x_408_ = lean_st_ref_take(v___y_402_);
v_env_409_ = lean_ctor_get(v___x_408_, 0);
v_nextMacroScope_410_ = lean_ctor_get(v___x_408_, 1);
v_ngen_411_ = lean_ctor_get(v___x_408_, 2);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_408_, 3);
v_traceState_413_ = lean_ctor_get(v___x_408_, 4);
v_cache_414_ = lean_ctor_get(v___x_408_, 5);
v_recordedDeps_415_ = lean_ctor_get(v___x_408_, 6);
v_messages_416_ = lean_ctor_get(v___x_408_, 7);
v_infoState_417_ = lean_ctor_get(v___x_408_, 8);
v_snapshotTasks_418_ = lean_ctor_get(v___x_408_, 9);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v___x_408_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_recordedDeps_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_ngen_411_);
lean_inc(v_nextMacroScope_410_);
lean_inc(v_env_409_);
lean_dec(v___x_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_MessageLog_add(v___x_407_, v_messages_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 7, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_env_409_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_nextMacroScope_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_ngen_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_traceState_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_recordedDeps_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 9, v_snapshotTasks_418_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_put(v___y_402_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_422_);
return v___x_427_;
}
}
}
v___jp_430_:
{
lean_object* v_fileName_439_; lean_object* v_fileMap_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_456_; 
v_fileName_439_ = lean_ctor_get(v___y_437_, 0);
v_fileMap_440_ = lean_ctor_get(v___y_437_, 1);
v___x_441_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_385_);
v___x_442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_441_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_456_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref_n(v_fileMap_440_, 2);
v___x_447_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_435_);
lean_dec(v___y_435_);
v___x_448_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_438_);
lean_dec(v___y_438_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_434_ == 0)
{
lean_del_object(v___x_445_);
lean_dec_ref(v___y_431_);
v___y_394_ = v_a_443_;
v___y_395_ = v___y_433_;
v___y_396_ = v___x_449_;
v___y_397_ = v___x_447_;
v___y_398_ = v___x_450_;
v___y_399_ = v_fileName_439_;
v___y_400_ = v___y_436_;
v_toCold_401_ = v___y_432_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
else
{
uint8_t v___x_451_; 
lean_inc(v_a_443_);
v___x_451_ = l_Lean_MessageData_hasTag(v___y_431_, v_a_443_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref_known(v___x_449_, 1);
lean_dec_ref(v___x_447_);
lean_dec(v_a_443_);
v___x_452_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_452_);
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_del_object(v___x_445_);
v___y_394_ = v_a_443_;
v___y_395_ = v___y_433_;
v___y_396_ = v___x_449_;
v___y_397_ = v___x_447_;
v___y_398_ = v___x_450_;
v___y_399_ = v_fileName_439_;
v___y_400_ = v___y_436_;
v_toCold_401_ = v___y_432_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Syntax_getTailPos_x3f(v___y_461_, v___y_463_);
lean_dec(v___y_461_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_inc(v___y_464_);
v___y_431_ = v___y_459_;
v___y_432_ = v___y_460_;
v___y_433_ = v___y_462_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_464_;
v___y_436_ = v___y_463_;
v___y_437_ = v___y_460_;
v___y_438_ = v___y_464_;
goto v___jp_430_;
}
else
{
lean_object* v_val_466_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___y_431_ = v___y_459_;
v___y_432_ = v___y_460_;
v___y_433_ = v___y_462_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_464_;
v___y_436_ = v___y_463_;
v___y_437_ = v___y_460_;
v___y_438_ = v_val_466_;
goto v___jp_430_;
}
}
v___jp_467_:
{
lean_object* v_toCold_470_; lean_object* v_ref_471_; uint8_t v_suppressElabErrors_472_; lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v_ref_475_; lean_object* v___x_476_; 
v_toCold_470_ = lean_ctor_get(v___y_390_, 0);
v_ref_471_ = lean_ctor_get(v___y_390_, 2);
v_suppressElabErrors_472_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*3 + 2);
v___x_473_ = lean_box(v_suppressElabErrors_472_);
v___f_474_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_474_, 0, v___x_473_);
v_ref_475_ = l_Lean_replaceRef(v_ref_384_, v_ref_471_);
v___x_476_ = l_Lean_Syntax_getPos_x3f(v_ref_475_, v___y_468_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___y_458_ = v_suppressElabErrors_472_;
v___y_459_ = v___f_474_;
v___y_460_ = v_toCold_470_;
v___y_461_ = v_ref_475_;
v___y_462_ = v___y_469_;
v___y_463_ = v___y_468_;
v___y_464_ = v___x_477_;
goto v___jp_457_;
}
else
{
lean_object* v_val_478_; 
v_val_478_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_476_, 1);
v___y_458_ = v_suppressElabErrors_472_;
v___y_459_ = v___f_474_;
v___y_460_ = v_toCold_470_;
v___y_461_ = v_ref_475_;
v___y_462_ = v___y_469_;
v___y_463_ = v___y_468_;
v___y_464_ = v_val_478_;
goto v___jp_457_;
}
}
v___jp_480_:
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 1;
v___x_483_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_482_);
if (v___x_483_ == 0)
{
v___y_468_ = v___y_481_;
v___y_469_ = v_severity_386_;
goto v___jp_467_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_390_);
v___x_485_ = l_Lean_warningAsError;
v___x_486_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_484_, v___x_485_);
lean_dec_ref(v___x_484_);
if (v___x_486_ == 0)
{
v___y_468_ = v___y_481_;
v___y_469_ = v_severity_386_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___y_481_;
v___y_469_ = v___x_479_;
goto v___jp_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_491_, lean_object* v_msgData_492_, lean_object* v_severity_493_, lean_object* v_isSilent_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v_severity_boxed_500_; uint8_t v_isSilent_boxed_501_; lean_object* v_res_502_; 
v_severity_boxed_500_ = lean_unbox(v_severity_493_);
v_isSilent_boxed_501_ = lean_unbox(v_isSilent_494_);
v_res_502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_491_, v_msgData_492_, v_severity_boxed_500_, v_isSilent_boxed_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v_ref_491_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_503_, uint8_t v_severity_504_, uint8_t v_isSilent_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_ref_515_; lean_object* v___x_516_; 
v_ref_515_ = lean_ctor_get(v___y_512_, 2);
v___x_516_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_515_, v_msgData_503_, v_severity_504_, v_isSilent_505_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_517_, lean_object* v_severity_518_, lean_object* v_isSilent_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_severity_boxed_529_; uint8_t v_isSilent_boxed_530_; lean_object* v_res_531_; 
v_severity_boxed_529_ = lean_unbox(v_severity_518_);
v_isSilent_boxed_530_ = lean_unbox(v_isSilent_519_);
v_res_531_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_517_, v_severity_boxed_529_, v_isSilent_boxed_530_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = 1;
v___x_543_ = 0;
v___x_544_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_532_, v___x_542_, v___x_543_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_env_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_595_; 
v___x_572_ = lean_st_ref_get(v___y_570_);
v_env_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_env_573_);
lean_dec(v___x_572_);
v___x_574_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_575_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_574_, v___y_569_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_595_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_595_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_595_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v_isExporting_585_; 
v_isExporting_585_ = lean_ctor_get_uint8(v_env_573_, sizeof(void*)*13);
lean_dec_ref(v_env_573_);
if (v_isExporting_585_ == 0)
{
lean_dec(v_a_576_);
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = l_Lean_isPrivateName(v_id_562_);
if (v___x_586_ == 0)
{
lean_dec(v_a_576_);
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = lean_unbox(v_a_576_);
lean_dec(v_a_576_);
if (v___x_587_ == 0)
{
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_578_);
v___x_588_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_589_ = 0;
v___x_590_ = l_Lean_MessageData_ofConstName(v_id_562_, v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_593_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_594_;
}
}
}
v___jp_580_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_box(0);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_607_, uint8_t v_enableLog_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v_toCold_619_; lean_object* v_env_620_; lean_object* v_currNamespace_621_; lean_object* v_openDecls_622_; lean_object* v___x_623_; lean_object* v_res_624_; lean_object* v___x_625_; 
v___x_618_ = lean_st_ref_get(v___y_616_);
v_toCold_619_ = lean_ctor_get(v___y_615_, 0);
v_env_620_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_618_);
v_currNamespace_621_ = lean_ctor_get(v_toCold_619_, 4);
v_openDecls_622_ = lean_ctor_get(v_toCold_619_, 5);
v___x_623_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_615_);
lean_inc(v_openDecls_622_);
lean_inc(v_currNamespace_621_);
v_res_624_ = l_Lean_ResolveName_resolveGlobalName(v_env_620_, v___x_623_, v_currNamespace_621_, v_openDecls_622_, v_id_607_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_st_ref_get(v___y_616_);
if (v_enableLog_608_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v___x_625_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_res_624_);
return v___x_626_;
}
else
{
lean_object* v_env_627_; uint8_t v_isExporting_628_; 
v_env_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_625_);
v_isExporting_628_ = lean_ctor_get_uint8(v_env_627_, sizeof(void*)*13);
lean_dec_ref(v_env_627_);
if (v_isExporting_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_res_624_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_624_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v_fst_632_; lean_object* v___x_633_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v_fst_632_ = lean_ctor_get(v_val_631_, 0);
lean_inc(v_fst_632_);
lean_dec(v_val_631_);
v___x_633_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_632_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_641_);
v___x_635_ = v___x_633_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_dec(v___x_633_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_res_624_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_res_624_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_res_624_);
v_a_642_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v___x_630_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_res_624_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_651_, lean_object* v_enableLog_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_enableLog_boxed_662_; lean_object* v_res_663_; 
v_enableLog_boxed_662_ = lean_unbox(v_enableLog_652_);
v_res_663_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_651_, v_enableLog_boxed_662_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
if (lean_obj_tag(v_a_664_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_List_reverse___redArg(v_a_665_);
return v___x_666_;
}
else
{
lean_object* v_head_667_; lean_object* v_tail_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_679_; 
v_head_667_ = lean_ctor_get(v_a_664_, 0);
v_tail_668_ = lean_ctor_get(v_a_664_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_679_ == 0)
{
v___x_670_ = v_a_664_;
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_tail_668_);
lean_inc(v_head_667_);
lean_dec(v_a_664_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_snd_672_; uint8_t v___x_673_; 
v_snd_672_ = lean_ctor_get(v_head_667_, 1);
v___x_673_ = l_List_isEmpty___redArg(v_snd_672_);
if (v___x_673_ == 0)
{
lean_del_object(v___x_670_);
lean_dec(v_head_667_);
v_a_664_ = v_tail_668_;
goto _start;
}
else
{
lean_object* v___x_676_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_a_665_);
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_head_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_665_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_a_664_ = v_tail_668_;
v_a_665_ = v___x_676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
if (lean_obj_tag(v_a_680_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_List_reverse___redArg(v_a_681_);
return v___x_682_;
}
else
{
lean_object* v_head_683_; lean_object* v_tail_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_head_683_ = lean_ctor_get(v_a_680_, 0);
v_tail_684_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v_a_680_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_tail_684_);
lean_inc(v_head_683_);
lean_dec(v_a_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v___x_690_; 
v_fst_688_ = lean_ctor_get(v_head_683_, 0);
lean_inc(v_fst_688_);
lean_dec(v_head_683_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_a_681_);
lean_ctor_set(v___x_686_, 0, v_fst_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_681_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_a_680_ = v_tail_684_;
v_a_681_ = v___x_690_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_ref_700_; lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_ref_700_ = lean_ctor_get(v___y_697_, 2);
v___x_701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc(v_ref_700_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_ref_700_);
lean_ctor_set(v___x_706_, 1, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 1);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_toCold_729_; lean_object* v_currRecDepth_730_; lean_object* v_ref_731_; uint16_t v_optionFlags_732_; uint8_t v_suppressElabErrors_733_; uint8_t v_checkDeprecated_734_; uint8_t v_isRecordingDeps_735_; lean_object* v_ref_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_toCold_729_ = lean_ctor_get(v___y_726_, 0);
v_currRecDepth_730_ = lean_ctor_get(v___y_726_, 1);
v_ref_731_ = lean_ctor_get(v___y_726_, 2);
v_optionFlags_732_ = lean_ctor_get_uint16(v___y_726_, sizeof(void*)*3);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*3 + 2);
v_checkDeprecated_734_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*3 + 3);
v_isRecordingDeps_735_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*3 + 4);
v_ref_736_ = l_Lean_replaceRef(v_ref_718_, v_ref_731_);
lean_inc(v_currRecDepth_730_);
lean_inc_ref(v_toCold_729_);
v___x_737_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_737_, 0, v_toCold_729_);
lean_ctor_set(v___x_737_, 1, v_currRecDepth_730_);
lean_ctor_set(v___x_737_, 2, v_ref_736_);
lean_ctor_set_uint16(v___x_737_, sizeof(void*)*3, v_optionFlags_732_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 2, v_suppressElabErrors_733_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 3, v_checkDeprecated_734_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 4, v_isRecordingDeps_735_);
v___x_738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_719_, v___y_724_, v___y_725_, v___x_737_, v___y_727_);
lean_dec_ref_known(v___x_737_, 3);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_739_, v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_ref_739_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
lean_ctor_set(v___x_757_, 3, v___x_756_);
lean_ctor_set(v___x_757_, 4, v___x_755_);
lean_ctor_set(v___x_757_, 5, v___x_755_);
lean_ctor_set(v___x_757_, 6, v___x_755_);
lean_ctor_set(v___x_757_, 7, v___x_755_);
lean_ctor_set(v___x_757_, 8, v___x_755_);
lean_ctor_set(v___x_757_, 9, v___x_755_);
lean_ctor_set(v___x_757_, 10, v___x_755_);
lean_ctor_set(v___x_757_, 11, v___x_754_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = lean_unsigned_to_nat(32u);
v___x_759_ = lean_mk_empty_array_with_capacity(v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_761_ = ((size_t)5ULL);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_unsigned_to_nat(32u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_766_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_762_);
lean_ctor_set(v___x_766_, 3, v___x_762_);
lean_ctor_set_usize(v___x_766_, 4, v___x_761_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_767_ = lean_box(1);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_767_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_792_, lean_object* v_declHint_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_env_798_; uint8_t v___x_799_; 
v___x_796_ = lean_box(0);
v___x_797_ = lean_st_ref_get(v___y_794_);
v_env_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_env_798_);
lean_dec(v___x_797_);
v___x_799_ = l_Lean_Name_isAnonymous(v_declHint_793_);
if (v___x_799_ == 0)
{
uint8_t v_isExporting_800_; 
v_isExporting_800_ = lean_ctor_get_uint8(v_env_798_, sizeof(void*)*13);
if (v_isExporting_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_env_798_);
lean_dec(v_declHint_793_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_msg_792_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; uint8_t v___x_803_; 
lean_inc_ref(v_env_798_);
v___x_802_ = l_Lean_Environment_setExporting(v_env_798_, v___x_799_);
lean_inc(v_declHint_793_);
lean_inc_ref(v___x_802_);
v___x_803_ = l_Lean_Environment_contains(v___x_802_, v_declHint_793_, v_isExporting_800_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v___x_802_);
lean_dec_ref(v_env_798_);
lean_dec(v_declHint_793_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_msg_792_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_c_810_; lean_object* v___x_811_; 
v___x_805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_807_ = l_Lean_Options_empty;
lean_inc_ref(v___x_802_);
v___x_808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_805_);
lean_ctor_set(v___x_808_, 2, v___x_806_);
lean_ctor_set(v___x_808_, 3, v___x_807_);
lean_inc(v_declHint_793_);
v___x_809_ = l_Lean_MessageData_ofConstName(v_declHint_793_, v___x_799_);
v_c_810_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_810_, 0, v___x_808_);
lean_ctor_set(v_c_810_, 1, v___x_809_);
v___x_811_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_802_, v_declHint_793_);
lean_dec_ref(v___x_802_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref(v_env_798_);
lean_dec(v_declHint_793_);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_c_810_);
v___x_814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_MessageData_note(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v_msg_792_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_853_; 
v_val_819_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_853_ == 0)
{
v___x_821_ = v___x_811_;
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v___x_811_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v_moduleNames_824_; lean_object* v_mod_825_; uint8_t v___x_826_; 
v___x_823_ = l_Lean_Environment_header(v_env_798_);
lean_dec_ref(v_env_798_);
v_moduleNames_824_ = lean_ctor_get(v___x_823_, 4);
lean_inc_ref(v_moduleNames_824_);
lean_dec_ref(v___x_823_);
v_mod_825_ = lean_array_get(v___x_796_, v_moduleNames_824_, v_val_819_);
lean_dec(v_val_819_);
lean_dec_ref(v_moduleNames_824_);
v___x_826_ = l_Lean_isPrivateName(v_declHint_793_);
lean_dec(v_declHint_793_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_c_810_);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_ofName(v_mod_825_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_MessageData_note(v___x_834_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v_msg_792_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_836_);
v___x_838_ = v___x_821_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_c_810_);
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Lean_MessageData_ofName(v_mod_825_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_MessageData_note(v___x_847_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v_msg_792_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_849_);
v___x_851_ = v___x_821_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_854_; 
lean_dec_ref(v_env_798_);
lean_dec(v_declHint_793_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_msg_792_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_855_, lean_object* v_declHint_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_855_, v_declHint_856_, v___y_857_);
lean_dec(v___y_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_860_, lean_object* v_declHint_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_881_; 
v___x_871_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_860_, v_declHint_861_, v___y_869_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_881_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_881_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_881_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_876_ = l_Lean_unknownIdentifierMessageTag;
v___x_877_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_877_);
v___x_879_ = v___x_874_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_882_, v_declHint_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_894_, lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_908_; 
v___x_906_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
v___x_908_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_894_, v_a_907_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_909_, lean_object* v_msg_910_, lean_object* v_declHint_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_909_, v_msg_910_, v_declHint_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v_ref_909_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_928_, lean_object* v_constName_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_939_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_940_ = 0;
lean_inc(v_constName_929_);
v___x_941_ = l_Lean_MessageData_ofConstName(v_constName_929_, v___x_940_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_939_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_928_, v___x_944_, v_constName_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_946_, lean_object* v_constName_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_946_, v_constName_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v_ref_946_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_958_, lean_object* v_cs_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_cs_970_; uint8_t v___x_974_; 
v___x_969_ = lean_box(0);
v_cs_970_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_959_, v___x_969_);
v___x_974_ = l_List_isEmpty___redArg(v_cs_970_);
if (v___x_974_ == 0)
{
lean_dec(v_n_958_);
goto v___jp_971_;
}
else
{
lean_object* v_ref_975_; lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_cs_970_);
v_ref_975_ = lean_ctor_get(v___y_966_, 2);
v___x_976_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_975_, v_n_958_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
v___jp_971_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_970_, v___x_969_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_985_, lean_object* v_cs_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_985_, v_cs_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = 1;
lean_inc(v_n_997_);
v___x_1008_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_997_, v___x_1007_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_997_, v_a_1009_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1010_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_n_997_);
v_a_1011_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1008_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
if (lean_obj_tag(v_a_1030_) == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_array_to_list(v_a_1031_);
return v___x_1032_;
}
else
{
lean_object* v_head_1033_; 
v_head_1033_ = lean_ctor_get(v_a_1030_, 0);
if (lean_obj_tag(v_head_1033_) == 1)
{
lean_object* v_fields_1034_; 
v_fields_1034_ = lean_ctor_get(v_head_1033_, 1);
if (lean_obj_tag(v_fields_1034_) == 0)
{
lean_object* v_tail_1035_; lean_object* v_n_1036_; lean_object* v___x_1037_; 
lean_inc_ref(v_head_1033_);
v_tail_1035_ = lean_ctor_get(v_a_1030_, 1);
lean_inc(v_tail_1035_);
lean_dec_ref_known(v_a_1030_, 2);
v_n_1036_ = lean_ctor_get(v_head_1033_, 0);
lean_inc(v_n_1036_);
lean_dec_ref_known(v_head_1033_, 2);
v___x_1037_ = lean_array_push(v_a_1031_, v_n_1036_);
v_a_1030_ = v_tail_1035_;
v_a_1031_ = v___x_1037_;
goto _start;
}
else
{
lean_object* v_tail_1039_; 
v_tail_1039_ = lean_ctor_get(v_a_1030_, 1);
lean_inc(v_tail_1039_);
lean_dec_ref_known(v_a_1030_, 2);
v_a_1030_ = v_tail_1039_;
goto _start;
}
}
else
{
lean_object* v_tail_1041_; 
v_tail_1041_ = lean_ctor_get(v_a_1030_, 1);
lean_inc(v_tail_1041_);
lean_dec_ref_known(v_a_1030_, 2);
v_a_1030_ = v_tail_1041_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1049_ = l_Lean_MessageData_ofFormat(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1050_, lean_object* v_k_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
if (lean_obj_tag(v_stx_1050_) == 3)
{
lean_object* v_val_1061_; lean_object* v_preresolved_1062_; lean_object* v___x_1063_; lean_object* v_pre_1064_; uint8_t v___x_1065_; 
v_val_1061_ = lean_ctor_get(v_stx_1050_, 2);
lean_inc(v_val_1061_);
v_preresolved_1062_ = lean_ctor_get(v_stx_1050_, 3);
v___x_1063_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1062_);
v_pre_1064_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1062_, v___x_1063_);
v___x_1065_ = l_List_isEmpty___redArg(v_pre_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v_val_1061_);
lean_dec_ref_known(v_stx_1050_, 4);
lean_dec_ref(v_k_1051_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_pre_1064_);
return v___x_1066_;
}
else
{
lean_object* v_toCold_1067_; lean_object* v_currRecDepth_1068_; lean_object* v_ref_1069_; uint16_t v_optionFlags_1070_; uint8_t v_suppressElabErrors_1071_; uint8_t v_checkDeprecated_1072_; uint8_t v_isRecordingDeps_1073_; lean_object* v_ref_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_pre_1064_);
v_toCold_1067_ = lean_ctor_get(v___y_1058_, 0);
v_currRecDepth_1068_ = lean_ctor_get(v___y_1058_, 1);
v_ref_1069_ = lean_ctor_get(v___y_1058_, 2);
v_optionFlags_1070_ = lean_ctor_get_uint16(v___y_1058_, sizeof(void*)*3);
v_suppressElabErrors_1071_ = lean_ctor_get_uint8(v___y_1058_, sizeof(void*)*3 + 2);
v_checkDeprecated_1072_ = lean_ctor_get_uint8(v___y_1058_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1073_ = lean_ctor_get_uint8(v___y_1058_, sizeof(void*)*3 + 4);
v_ref_1074_ = l_Lean_replaceRef(v_stx_1050_, v_ref_1069_);
lean_dec_ref_known(v_stx_1050_, 4);
lean_inc(v_currRecDepth_1068_);
lean_inc_ref(v_toCold_1067_);
v___x_1075_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1075_, 0, v_toCold_1067_);
lean_ctor_set(v___x_1075_, 1, v_currRecDepth_1068_);
lean_ctor_set(v___x_1075_, 2, v_ref_1074_);
lean_ctor_set_uint16(v___x_1075_, sizeof(void*)*3, v_optionFlags_1070_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 2, v_suppressElabErrors_1071_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 3, v_checkDeprecated_1072_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 4, v_isRecordingDeps_1073_);
lean_inc(v___y_1059_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v___x_1076_ = lean_apply_10(v_k_1051_, v_val_1061_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___x_1075_, v___y_1059_, lean_box(0));
return v___x_1076_;
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec_ref(v_k_1051_);
v___x_1077_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1078_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1050_, v___x_1077_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v_stx_1050_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1079_, lean_object* v_k_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1079_, v_k_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1103_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1092_, v___x_1102_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1115_, size_t v_sz_1116_, size_t v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_usize_dec_lt(v_i_1117_, v_sz_1116_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_b_1118_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v_name_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_a_1130_ = lean_array_uget_borrowed(v_as_1115_, v_i_1117_);
v_name_1131_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_name_1131_);
v___x_1132_ = l_Lean_mkIdent(v_name_1131_);
lean_inc(v___x_1132_);
v___x_1133_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1132_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1132_, v_a_1134_, v_b_1118_, v___y_1125_);
lean_dec(v_a_1134_);
lean_dec(v___x_1132_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; size_t v___x_1137_; size_t v___x_1138_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_add(v_i_1117_, v___x_1137_);
v_i_1117_ = v___x_1138_;
v_b_1118_ = v_a_1136_;
goto _start;
}
else
{
return v___x_1135_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___x_1132_);
lean_dec_ref(v_b_1118_);
v_a_1140_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1133_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1133_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1148_, v_sz_boxed_1161_, v_i_boxed_1162_, v_b_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_as_1148_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1183_, lean_object* v_stx_1184_, uint8_t v___x_1185_, lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v___f_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
if (v___x_1183_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v_tk_1201_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v_stxForSuggestion_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1463_; uint8_t v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v_stxForExecution_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; uint8_t v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; uint8_t v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v_argsArray_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1778_; lean_object* v___y_1779_; uint8_t v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_args_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___x_1936_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v_o_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_bang_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v_tk_1201_ = l_Lean_Syntax_getArg(v_stx_1184_, v___x_1200_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1994_ = l_Lean_Syntax_getArg(v_stx_1184_, v___x_1936_);
v___x_1995_ = l_Lean_Syntax_isNone(v___x_1994_);
if (v___x_1995_ == 0)
{
uint8_t v___x_1996_; 
lean_inc(v___x_1994_);
v___x_1996_ = l_Lean_Syntax_matchesNull(v___x_1994_, v___x_1936_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec(v___x_1994_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1997_;
}
else
{
lean_object* v_bang_1998_; lean_object* v___x_1999_; 
v_bang_1998_ = l_Lean_Syntax_getArg(v___x_1994_, v___x_1200_);
lean_dec(v___x_1994_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_bang_1998_);
v_bang_1966_ = v___x_1999_;
v___y_1967_ = v___y_1190_;
v___y_1968_ = v___y_1191_;
v___y_1969_ = v___y_1192_;
v___y_1970_ = v___y_1193_;
v___y_1971_ = v___y_1194_;
v___y_1972_ = v___y_1195_;
v___y_1973_ = v___y_1196_;
v___y_1974_ = v___y_1197_;
goto v___jp_1965_;
}
}
else
{
lean_object* v___x_2000_; 
lean_dec(v___x_1994_);
v___x_2000_ = lean_box(0);
v_bang_1966_ = v___x_2000_;
v___y_1967_ = v___y_1190_;
v___y_1968_ = v___y_1191_;
v___y_1969_ = v___y_1192_;
v___y_1970_ = v___y_1193_;
v___y_1971_ = v___y_1194_;
v___y_1972_ = v___y_1195_;
v___y_1973_ = v___y_1196_;
v___y_1974_ = v___y_1197_;
goto v___jp_1965_;
}
v___jp_1202_:
{
lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(v___x_1185_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1217_, 0, v___y_1205_);
lean_closure_set(v___f_1217_, 1, v___x_1200_);
lean_closure_set(v___f_1217_, 2, v___x_1216_);
lean_closure_set(v___f_1217_, 3, v___y_1215_);
lean_closure_set(v___f_1217_, 4, v___y_1203_);
v___x_1218_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1204_, v___f_1217_, v___y_1209_, v___y_1206_, v___y_1210_, v___y_1207_, v___y_1213_, v___y_1212_, v___y_1211_, v___y_1208_);
lean_dec(v___y_1204_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v_usedTheorems_1220_; lean_object* v_diag_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1263_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_usedTheorems_1220_ = lean_ctor_get(v_a_1219_, 0);
v_diag_1221_ = lean_ctor_get(v_a_1219_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1223_ = v_a_1219_;
v_isShared_1224_ = v_isSharedCheck_1263_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_diag_1221_);
lean_inc(v_usedTheorems_1220_);
lean_dec(v_a_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1263_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1214_, v_usedTheorems_1220_, v___y_1213_, v___y_1212_, v___y_1211_, v___y_1208_);
lean_dec_ref(v_usedTheorems_1220_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_ref_1227_ = lean_ctor_get(v___y_1211_, 2);
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v_a_1226_);
lean_ctor_set(v___x_1223_, 0, v___x_1228_);
v___x_1230_ = v___x_1223_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1226_);
v___x_1230_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
lean_ctor_set(v___x_1232_, 3, v___x_1231_);
lean_ctor_set(v___x_1232_, 4, v___x_1231_);
lean_ctor_set(v___x_1232_, 5, v___x_1231_);
lean_inc(v_ref_1227_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_ref_1227_);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1235_ = 4;
v___x_1236_ = l_Lean_MessageData_nil;
v___x_1237_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1201_, v___x_1232_, v___x_1233_, v___x_1234_, v___x_1231_, v___x_1235_, v___x_1236_, v___y_1211_, v___y_1208_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1245_);
v___x_1239_ = v___x_1237_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___x_1237_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_diag_1221_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_diag_1221_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_diag_1221_);
v_a_1246_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1237_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1237_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_del_object(v___x_1223_);
lean_dec_ref(v_diag_1221_);
lean_dec(v_tk_1201_);
v_a_1255_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1225_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1225_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___y_1214_);
lean_dec(v_tk_1201_);
v_a_1264_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1218_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1218_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
v___jp_1272_:
{
uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = 0;
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1288_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1275_, v___x_1286_, v___y_1274_, v___x_1286_, v___x_1287_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1275_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
if (lean_obj_tag(v___y_1276_) == 0)
{
lean_object* v_ctx_1290_; lean_object* v_simprocs_1291_; lean_object* v_dischargeWrapper_1292_; 
v_ctx_1290_ = lean_ctor_get(v_a_1289_, 0);
lean_inc_ref(v_ctx_1290_);
v_simprocs_1291_ = lean_ctor_get(v_a_1289_, 1);
lean_inc_ref(v_simprocs_1291_);
v_dischargeWrapper_1292_ = lean_ctor_get(v_a_1289_, 2);
lean_inc(v_dischargeWrapper_1292_);
lean_dec(v_a_1289_);
v___y_1203_ = v_simprocs_1291_;
v___y_1204_ = v_dischargeWrapper_1292_;
v___y_1205_ = v___y_1273_;
v___y_1206_ = v___y_1279_;
v___y_1207_ = v___y_1281_;
v___y_1208_ = v___y_1285_;
v___y_1209_ = v___y_1278_;
v___y_1210_ = v___y_1280_;
v___y_1211_ = v___y_1284_;
v___y_1212_ = v___y_1283_;
v___y_1213_ = v___y_1282_;
v___y_1214_ = v_stxForSuggestion_1277_;
v___y_1215_ = v_ctx_1290_;
goto v___jp_1202_;
}
else
{
lean_object* v_ctx_1293_; lean_object* v_simprocs_1294_; lean_object* v_dischargeWrapper_1295_; lean_object* v___x_1296_; 
lean_dec_ref_known(v___y_1276_, 1);
v_ctx_1293_ = lean_ctor_get(v_a_1289_, 0);
lean_inc_ref(v_ctx_1293_);
v_simprocs_1294_ = lean_ctor_get(v_a_1289_, 1);
lean_inc_ref(v_simprocs_1294_);
v_dischargeWrapper_1295_ = lean_ctor_get(v_a_1289_, 2);
lean_inc(v_dischargeWrapper_1295_);
lean_dec(v_a_1289_);
v___x_1296_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1293_);
v___y_1203_ = v_simprocs_1294_;
v___y_1204_ = v_dischargeWrapper_1295_;
v___y_1205_ = v___y_1273_;
v___y_1206_ = v___y_1279_;
v___y_1207_ = v___y_1281_;
v___y_1208_ = v___y_1285_;
v___y_1209_ = v___y_1278_;
v___y_1210_ = v___y_1280_;
v___y_1211_ = v___y_1284_;
v___y_1212_ = v___y_1283_;
v___y_1213_ = v___y_1282_;
v___y_1214_ = v_stxForSuggestion_1277_;
v___y_1215_ = v___x_1296_;
goto v___jp_1202_;
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_stxForSuggestion_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1273_);
lean_dec(v_tk_1201_);
v_a_1297_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1288_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1288_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
v___jp_1305_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc_ref(v___y_1316_);
v___x_1328_ = l_Array_append___redArg(v___y_1316_, v___y_1327_);
lean_dec_ref(v___y_1327_);
lean_inc(v___y_1324_);
lean_inc(v___y_1307_);
v___x_1329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1329_, 0, v___y_1307_);
lean_ctor_set(v___x_1329_, 1, v___y_1324_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
v___x_1330_ = l_Lean_Syntax_node6(v___y_1307_, v___y_1311_, v___y_1312_, v___y_1325_, v___y_1313_, v___y_1308_, v___y_1321_, v___x_1329_);
v___y_1273_ = v___y_1306_;
v___y_1274_ = v___y_1309_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1322_;
v_stxForSuggestion_1277_ = v___x_1330_;
v___y_1278_ = v___y_1326_;
v___y_1279_ = v___y_1315_;
v___y_1280_ = v___y_1318_;
v___y_1281_ = v___y_1314_;
v___y_1282_ = v___y_1319_;
v___y_1283_ = v___y_1320_;
v___y_1284_ = v___y_1323_;
v___y_1285_ = v___y_1310_;
goto v___jp_1272_;
}
v___jp_1331_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref_n(v___y_1343_, 2);
v___x_1354_ = l_Array_append___redArg(v___y_1343_, v___y_1353_);
lean_dec_ref(v___y_1353_);
lean_inc_n(v___y_1350_, 3);
lean_inc_n(v___y_1333_, 5);
v___x_1355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1333_);
lean_ctor_set(v___x_1355_, 1, v___y_1350_);
lean_ctor_set(v___x_1355_, 2, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1333_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1359_ = l_Lean_Syntax_SepArray_ofElems(v___x_1358_, v___y_1338_);
lean_dec_ref(v___y_1338_);
v___x_1360_ = l_Array_append___redArg(v___y_1343_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1333_);
lean_ctor_set(v___x_1361_, 1, v___y_1350_);
lean_ctor_set(v___x_1361_, 2, v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1333_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_Syntax_node3(v___y_1333_, v___y_1350_, v___x_1357_, v___x_1361_, v___x_1363_);
if (lean_obj_tag(v___y_1342_) == 1)
{
lean_object* v_val_1365_; lean_object* v___x_1366_; 
v_val_1365_ = lean_ctor_get(v___y_1342_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___y_1342_, 1);
v___x_1366_ = l_Array_mkArray1___redArg(v_val_1365_);
v___y_1306_ = v___y_1332_;
v___y_1307_ = v___y_1333_;
v___y_1308_ = v___x_1355_;
v___y_1309_ = v___y_1334_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1336_;
v___y_1312_ = v___y_1337_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1340_;
v___y_1315_ = v___y_1341_;
v___y_1316_ = v___y_1343_;
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___x_1364_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1350_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1351_;
v___y_1327_ = v___x_1366_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1367_; 
lean_dec(v___y_1342_);
v___x_1367_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1306_ = v___y_1332_;
v___y_1307_ = v___y_1333_;
v___y_1308_ = v___x_1355_;
v___y_1309_ = v___y_1334_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1336_;
v___y_1312_ = v___y_1337_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1340_;
v___y_1315_ = v___y_1341_;
v___y_1316_ = v___y_1343_;
v___y_1317_ = v___y_1344_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___x_1364_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1350_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1351_;
v___y_1327_ = v___x_1367_;
goto v___jp_1305_;
}
}
v___jp_1368_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_inc_ref(v___y_1379_);
v___x_1391_ = l_Array_append___redArg(v___y_1379_, v___y_1390_);
lean_dec_ref(v___y_1390_);
lean_inc(v___y_1387_);
lean_inc(v___y_1370_);
v___x_1392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1370_);
lean_ctor_set(v___x_1392_, 1, v___y_1387_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
if (lean_obj_tag(v___y_1377_) == 1)
{
lean_object* v_val_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_val_1393_ = lean_ctor_get(v___y_1377_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v___y_1377_, 1);
v___x_1394_ = l_Lean_SourceInfo_fromRef(v_val_1393_, v___x_1185_);
lean_dec(v_val_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Array_mkArray1___redArg(v___x_1396_);
v___y_1332_ = v___y_1369_;
v___y_1333_ = v___y_1370_;
v___y_1334_ = v___y_1371_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v___y_1373_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v___x_1392_;
v___y_1340_ = v___y_1376_;
v___y_1341_ = v___y_1378_;
v___y_1342_ = v___y_1380_;
v___y_1343_ = v___y_1379_;
v___y_1344_ = v___y_1381_;
v___y_1345_ = v___y_1382_;
v___y_1346_ = v___y_1383_;
v___y_1347_ = v___y_1384_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1385_;
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1389_;
v___y_1352_ = v___y_1388_;
v___y_1353_ = v___x_1397_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1398_; 
lean_dec(v___y_1377_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1332_ = v___y_1369_;
v___y_1333_ = v___y_1370_;
v___y_1334_ = v___y_1371_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v___y_1373_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v___x_1392_;
v___y_1340_ = v___y_1376_;
v___y_1341_ = v___y_1378_;
v___y_1342_ = v___y_1380_;
v___y_1343_ = v___y_1379_;
v___y_1344_ = v___y_1381_;
v___y_1345_ = v___y_1382_;
v___y_1346_ = v___y_1383_;
v___y_1347_ = v___y_1384_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1385_;
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1389_;
v___y_1352_ = v___y_1388_;
v___y_1353_ = v___x_1398_;
goto v___jp_1331_;
}
}
v___jp_1399_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_inc_ref(v___y_1406_);
v___x_1422_ = l_Array_append___redArg(v___y_1406_, v___y_1421_);
lean_dec_ref(v___y_1421_);
lean_inc(v___y_1407_);
lean_inc(v___y_1409_);
v___x_1423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1409_);
lean_ctor_set(v___x_1423_, 1, v___y_1407_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
v___x_1424_ = l_Lean_Syntax_node6(v___y_1409_, v___y_1410_, v___y_1404_, v___y_1419_, v___y_1416_, v___y_1411_, v___y_1402_, v___x_1423_);
v___y_1273_ = v___y_1400_;
v___y_1274_ = v___y_1401_;
v___y_1275_ = v___y_1412_;
v___y_1276_ = v___y_1417_;
v_stxForSuggestion_1277_ = v___x_1424_;
v___y_1278_ = v___y_1420_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1413_;
v___y_1281_ = v___y_1405_;
v___y_1282_ = v___y_1414_;
v___y_1283_ = v___y_1415_;
v___y_1284_ = v___y_1418_;
v___y_1285_ = v___y_1403_;
goto v___jp_1272_;
}
v___jp_1425_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_inc_ref_n(v___y_1432_, 2);
v___x_1448_ = l_Array_append___redArg(v___y_1432_, v___y_1447_);
lean_dec_ref(v___y_1447_);
lean_inc_n(v___y_1433_, 3);
lean_inc_n(v___y_1436_, 5);
v___x_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1436_);
lean_ctor_set(v___x_1449_, 1, v___y_1433_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1436_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1453_ = l_Lean_Syntax_SepArray_ofElems(v___x_1452_, v___y_1430_);
lean_dec_ref(v___y_1430_);
v___x_1454_ = l_Array_append___redArg(v___y_1432_, v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1436_);
lean_ctor_set(v___x_1455_, 1, v___y_1433_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1436_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_Syntax_node3(v___y_1436_, v___y_1433_, v___x_1451_, v___x_1455_, v___x_1457_);
if (lean_obj_tag(v___y_1435_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1460_; 
v_val_1459_ = lean_ctor_get(v___y_1435_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v___y_1435_, 1);
v___x_1460_ = l_Array_mkArray1___redArg(v_val_1459_);
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1427_;
v___y_1402_ = v___x_1458_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1429_;
v___y_1405_ = v___y_1431_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1436_;
v___y_1410_ = v___y_1437_;
v___y_1411_ = v___x_1449_;
v___y_1412_ = v___y_1438_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1442_;
v___y_1416_ = v___y_1441_;
v___y_1417_ = v___y_1444_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___y_1446_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___x_1460_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v___y_1435_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1427_;
v___y_1402_ = v___x_1458_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1429_;
v___y_1405_ = v___y_1431_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1436_;
v___y_1410_ = v___y_1437_;
v___y_1411_ = v___x_1449_;
v___y_1412_ = v___y_1438_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1442_;
v___y_1416_ = v___y_1441_;
v___y_1417_ = v___y_1444_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___y_1446_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___x_1461_;
goto v___jp_1399_;
}
}
v___jp_1462_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_inc_ref(v___y_1469_);
v___x_1485_ = l_Array_append___redArg(v___y_1469_, v___y_1484_);
lean_dec_ref(v___y_1484_);
lean_inc(v___y_1470_);
lean_inc(v___y_1474_);
v___x_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1474_);
lean_ctor_set(v___x_1486_, 1, v___y_1470_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
if (lean_obj_tag(v___y_1471_) == 1)
{
lean_object* v_val_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_val_1487_ = lean_ctor_get(v___y_1471_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v___y_1471_, 1);
v___x_1488_ = l_Lean_SourceInfo_fromRef(v_val_1487_, v___x_1185_);
lean_dec(v_val_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Array_mkArray1___redArg(v___x_1490_);
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1464_;
v___y_1428_ = v___y_1465_;
v___y_1429_ = v___y_1466_;
v___y_1430_ = v___y_1467_;
v___y_1431_ = v___y_1468_;
v___y_1432_ = v___y_1469_;
v___y_1433_ = v___y_1470_;
v___y_1434_ = v___y_1472_;
v___y_1435_ = v___y_1473_;
v___y_1436_ = v___y_1474_;
v___y_1437_ = v___y_1475_;
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___y_1477_;
v___y_1440_ = v___y_1478_;
v___y_1441_ = v___x_1486_;
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___y_1481_;
v___y_1444_ = v___y_1480_;
v___y_1445_ = v___y_1483_;
v___y_1446_ = v___y_1482_;
v___y_1447_ = v___x_1491_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v___y_1471_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1464_;
v___y_1428_ = v___y_1465_;
v___y_1429_ = v___y_1466_;
v___y_1430_ = v___y_1467_;
v___y_1431_ = v___y_1468_;
v___y_1432_ = v___y_1469_;
v___y_1433_ = v___y_1470_;
v___y_1434_ = v___y_1472_;
v___y_1435_ = v___y_1473_;
v___y_1436_ = v___y_1474_;
v___y_1437_ = v___y_1475_;
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___y_1477_;
v___y_1440_ = v___y_1478_;
v___y_1441_ = v___x_1486_;
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___y_1481_;
v___y_1444_ = v___y_1480_;
v___y_1445_ = v___y_1483_;
v___y_1446_ = v___y_1482_;
v___y_1447_ = v___x_1492_;
goto v___jp_1425_;
}
}
v___jp_1493_:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1499_);
if (lean_obj_tag(v___y_1501_) == 0)
{
lean_object* v_a_1512_; lean_object* v_ref_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1511_);
v_ref_1513_ = lean_ctor_get(v___y_1509_, 2);
v___x_1514_ = 0;
v___x_1515_ = l_Lean_SourceInfo_fromRef(v_ref_1513_, v___x_1514_);
v___x_1516_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1517_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1516_);
v___x_1518_ = l_Lean_SourceInfo_fromRef(v_tk_1201_, v___x_1185_);
v___x_1519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1516_);
v___x_1520_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1521_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1495_) == 1)
{
lean_object* v_val_1522_; lean_object* v___x_1523_; 
v_val_1522_ = lean_ctor_get(v___y_1495_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___y_1495_, 1);
v___x_1523_ = l_Array_mkArray1___redArg(v_val_1522_);
v___y_1463_ = v___y_1494_;
v___y_1464_ = v___y_1498_;
v___y_1465_ = v___y_1510_;
v___y_1466_ = v___x_1519_;
v___y_1467_ = v___y_1500_;
v___y_1468_ = v___y_1506_;
v___y_1469_ = v___x_1521_;
v___y_1470_ = v___x_1520_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1504_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___x_1515_;
v___y_1475_ = v___x_1517_;
v___y_1476_ = v_stxForExecution_1502_;
v___y_1477_ = v___y_1505_;
v___y_1478_ = v___y_1507_;
v___y_1479_ = v___y_1508_;
v___y_1480_ = v___y_1501_;
v___y_1481_ = v___y_1509_;
v___y_1482_ = v_a_1512_;
v___y_1483_ = v___y_1503_;
v___y_1484_ = v___x_1523_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1524_; 
lean_dec(v___y_1495_);
v___x_1524_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1463_ = v___y_1494_;
v___y_1464_ = v___y_1498_;
v___y_1465_ = v___y_1510_;
v___y_1466_ = v___x_1519_;
v___y_1467_ = v___y_1500_;
v___y_1468_ = v___y_1506_;
v___y_1469_ = v___x_1521_;
v___y_1470_ = v___x_1520_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1504_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___x_1515_;
v___y_1475_ = v___x_1517_;
v___y_1476_ = v_stxForExecution_1502_;
v___y_1477_ = v___y_1505_;
v___y_1478_ = v___y_1507_;
v___y_1479_ = v___y_1508_;
v___y_1480_ = v___y_1501_;
v___y_1481_ = v___y_1509_;
v___y_1482_ = v_a_1512_;
v___y_1483_ = v___y_1503_;
v___y_1484_ = v___x_1524_;
goto v___jp_1462_;
}
}
else
{
lean_object* v_a_1525_; lean_object* v_ref_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_a_1525_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1511_);
v_ref_1526_ = lean_ctor_get(v___y_1509_, 2);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_ref_1526_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1530_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1529_);
v___x_1531_ = l_Lean_SourceInfo_fromRef(v_tk_1201_, v___x_1185_);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1535_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1495_) == 1)
{
lean_object* v_val_1536_; lean_object* v___x_1537_; 
v_val_1536_ = lean_ctor_get(v___y_1495_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___y_1495_, 1);
v___x_1537_ = l_Array_mkArray1___redArg(v_val_1536_);
v___y_1369_ = v___y_1494_;
v___y_1370_ = v___x_1528_;
v___y_1371_ = v___y_1498_;
v___y_1372_ = v___y_1510_;
v___y_1373_ = v___x_1530_;
v___y_1374_ = v___x_1533_;
v___y_1375_ = v___y_1500_;
v___y_1376_ = v___y_1506_;
v___y_1377_ = v___y_1496_;
v___y_1378_ = v___y_1504_;
v___y_1379_ = v___x_1535_;
v___y_1380_ = v___y_1497_;
v___y_1381_ = v_stxForExecution_1502_;
v___y_1382_ = v___y_1505_;
v___y_1383_ = v___y_1507_;
v___y_1384_ = v___y_1508_;
v___y_1385_ = v___y_1501_;
v___y_1386_ = v___y_1509_;
v___y_1387_ = v___x_1534_;
v___y_1388_ = v_a_1525_;
v___y_1389_ = v___y_1503_;
v___y_1390_ = v___x_1537_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1538_; 
lean_dec(v___y_1495_);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1369_ = v___y_1494_;
v___y_1370_ = v___x_1528_;
v___y_1371_ = v___y_1498_;
v___y_1372_ = v___y_1510_;
v___y_1373_ = v___x_1530_;
v___y_1374_ = v___x_1533_;
v___y_1375_ = v___y_1500_;
v___y_1376_ = v___y_1506_;
v___y_1377_ = v___y_1496_;
v___y_1378_ = v___y_1504_;
v___y_1379_ = v___x_1535_;
v___y_1380_ = v___y_1497_;
v___y_1381_ = v_stxForExecution_1502_;
v___y_1382_ = v___y_1505_;
v___y_1383_ = v___y_1507_;
v___y_1384_ = v___y_1508_;
v___y_1385_ = v___y_1501_;
v___y_1386_ = v___y_1509_;
v___y_1387_ = v___x_1534_;
v___y_1388_ = v_a_1525_;
v___y_1389_ = v___y_1503_;
v___y_1390_ = v___x_1538_;
goto v___jp_1368_;
}
}
}
v___jp_1539_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_inc_ref(v___y_1545_);
v___x_1565_ = l_Array_append___redArg(v___y_1545_, v___y_1564_);
lean_dec_ref(v___y_1564_);
lean_inc(v___y_1542_);
lean_inc(v___y_1562_);
v___x_1566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1562_);
lean_ctor_set(v___x_1566_, 1, v___y_1542_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
lean_inc(v___y_1558_);
v___x_1567_ = l_Lean_Syntax_node6(v___y_1562_, v___y_1548_, v___y_1541_, v___y_1558_, v___y_1563_, v___y_1550_, v___y_1555_, v___x_1566_);
v___y_1494_ = v___y_1540_;
v___y_1495_ = v___y_1552_;
v___y_1496_ = v___y_1553_;
v___y_1497_ = v___y_1554_;
v___y_1498_ = v___y_1546_;
v___y_1499_ = v___y_1558_;
v___y_1500_ = v___y_1549_;
v___y_1501_ = v___y_1561_;
v_stxForExecution_1502_ = v___x_1567_;
v___y_1503_ = v___y_1560_;
v___y_1504_ = v___y_1557_;
v___y_1505_ = v___y_1556_;
v___y_1506_ = v___y_1559_;
v___y_1507_ = v___y_1543_;
v___y_1508_ = v___y_1547_;
v___y_1509_ = v___y_1544_;
v___y_1510_ = v___y_1551_;
goto v___jp_1493_;
}
v___jp_1568_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_inc_ref_n(v___y_1574_, 2);
v___x_1592_ = l_Array_append___redArg(v___y_1574_, v___y_1591_);
lean_dec_ref(v___y_1591_);
lean_inc_n(v___y_1571_, 3);
lean_inc_n(v___y_1590_, 5);
v___x_1593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1593_, 0, v___y_1590_);
lean_ctor_set(v___x_1593_, 1, v___y_1571_);
lean_ctor_set(v___x_1593_, 2, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___y_1590_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1597_ = l_Lean_Syntax_SepArray_ofElems(v___x_1596_, v___y_1578_);
v___x_1598_ = l_Array_append___redArg(v___y_1574_, v___x_1597_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1590_);
lean_ctor_set(v___x_1599_, 1, v___y_1571_);
lean_ctor_set(v___x_1599_, 2, v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___y_1590_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_Syntax_node3(v___y_1590_, v___y_1571_, v___x_1595_, v___x_1599_, v___x_1601_);
if (lean_obj_tag(v___y_1582_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1604_; 
v_val_1603_ = lean_ctor_get(v___y_1582_, 0);
lean_inc(v_val_1603_);
v___x_1604_ = l_Array_mkArray1___redArg(v_val_1603_);
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1570_;
v___y_1542_ = v___y_1571_;
v___y_1543_ = v___y_1572_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1575_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1577_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___x_1593_;
v___y_1551_ = v___y_1579_;
v___y_1552_ = v___y_1580_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1582_;
v___y_1555_ = v___x_1602_;
v___y_1556_ = v___y_1583_;
v___y_1557_ = v___y_1584_;
v___y_1558_ = v___y_1585_;
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1589_;
v___y_1562_ = v___y_1590_;
v___y_1563_ = v___y_1588_;
v___y_1564_ = v___x_1604_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1570_;
v___y_1542_ = v___y_1571_;
v___y_1543_ = v___y_1572_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1575_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1577_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___x_1593_;
v___y_1551_ = v___y_1579_;
v___y_1552_ = v___y_1580_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1582_;
v___y_1555_ = v___x_1602_;
v___y_1556_ = v___y_1583_;
v___y_1557_ = v___y_1584_;
v___y_1558_ = v___y_1585_;
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1589_;
v___y_1562_ = v___y_1590_;
v___y_1563_ = v___y_1588_;
v___y_1564_ = v___x_1605_;
goto v___jp_1539_;
}
}
v___jp_1606_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_inc_ref(v___y_1612_);
v___x_1629_ = l_Array_append___redArg(v___y_1612_, v___y_1628_);
lean_dec_ref(v___y_1628_);
lean_inc(v___y_1609_);
lean_inc(v___y_1627_);
v___x_1630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1630_, 0, v___y_1627_);
lean_ctor_set(v___x_1630_, 1, v___y_1609_);
lean_ctor_set(v___x_1630_, 2, v___x_1629_);
if (lean_obj_tag(v___y_1619_) == 1)
{
lean_object* v_val_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_val_1631_ = lean_ctor_get(v___y_1619_, 0);
v___x_1632_ = l_Lean_SourceInfo_fromRef(v_val_1631_, v___x_1185_);
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Array_mkArray1___redArg(v___x_1634_);
v___y_1569_ = v___y_1607_;
v___y_1570_ = v___y_1608_;
v___y_1571_ = v___y_1609_;
v___y_1572_ = v___y_1610_;
v___y_1573_ = v___y_1611_;
v___y_1574_ = v___y_1612_;
v___y_1575_ = v___y_1613_;
v___y_1576_ = v___y_1614_;
v___y_1577_ = v___y_1615_;
v___y_1578_ = v___y_1616_;
v___y_1579_ = v___y_1617_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v___y_1619_;
v___y_1582_ = v___y_1620_;
v___y_1583_ = v___y_1621_;
v___y_1584_ = v___y_1622_;
v___y_1585_ = v___y_1623_;
v___y_1586_ = v___y_1624_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___x_1630_;
v___y_1589_ = v___y_1626_;
v___y_1590_ = v___y_1627_;
v___y_1591_ = v___x_1635_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1569_ = v___y_1607_;
v___y_1570_ = v___y_1608_;
v___y_1571_ = v___y_1609_;
v___y_1572_ = v___y_1610_;
v___y_1573_ = v___y_1611_;
v___y_1574_ = v___y_1612_;
v___y_1575_ = v___y_1613_;
v___y_1576_ = v___y_1614_;
v___y_1577_ = v___y_1615_;
v___y_1578_ = v___y_1616_;
v___y_1579_ = v___y_1617_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v___y_1619_;
v___y_1582_ = v___y_1620_;
v___y_1583_ = v___y_1621_;
v___y_1584_ = v___y_1622_;
v___y_1585_ = v___y_1623_;
v___y_1586_ = v___y_1624_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___x_1630_;
v___y_1589_ = v___y_1626_;
v___y_1590_ = v___y_1627_;
v___y_1591_ = v___x_1636_;
goto v___jp_1568_;
}
}
v___jp_1637_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_inc_ref(v___y_1660_);
v___x_1663_ = l_Array_append___redArg(v___y_1660_, v___y_1662_);
lean_dec_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc(v___y_1642_);
v___x_1664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1642_);
lean_ctor_set(v___x_1664_, 1, v___y_1661_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
lean_inc(v___y_1654_);
v___x_1665_ = l_Lean_Syntax_node6(v___y_1642_, v___y_1646_, v___y_1657_, v___y_1654_, v___y_1648_, v___y_1655_, v___y_1639_, v___x_1664_);
v___y_1494_ = v___y_1638_;
v___y_1495_ = v___y_1649_;
v___y_1496_ = v___y_1650_;
v___y_1497_ = v___y_1651_;
v___y_1498_ = v___y_1643_;
v___y_1499_ = v___y_1654_;
v___y_1500_ = v___y_1645_;
v___y_1501_ = v___y_1659_;
v_stxForExecution_1502_ = v___x_1665_;
v___y_1503_ = v___y_1658_;
v___y_1504_ = v___y_1653_;
v___y_1505_ = v___y_1652_;
v___y_1506_ = v___y_1656_;
v___y_1507_ = v___y_1640_;
v___y_1508_ = v___y_1644_;
v___y_1509_ = v___y_1641_;
v___y_1510_ = v___y_1647_;
goto v___jp_1493_;
}
v___jp_1666_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_inc_ref_n(v___y_1687_, 2);
v___x_1690_ = l_Array_append___redArg(v___y_1687_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_inc_n(v___y_1688_, 3);
lean_inc_n(v___y_1669_, 5);
v___x_1691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1669_);
lean_ctor_set(v___x_1691_, 1, v___y_1688_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1669_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1695_ = l_Lean_Syntax_SepArray_ofElems(v___x_1694_, v___y_1673_);
v___x_1696_ = l_Array_append___redArg(v___y_1687_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1669_);
lean_ctor_set(v___x_1697_, 1, v___y_1688_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1669_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_Syntax_node3(v___y_1669_, v___y_1688_, v___x_1693_, v___x_1697_, v___x_1699_);
if (lean_obj_tag(v___y_1679_) == 1)
{
lean_object* v_val_1701_; lean_object* v___x_1702_; 
v_val_1701_ = lean_ctor_get(v___y_1679_, 0);
lean_inc(v_val_1701_);
v___x_1702_ = l_Array_mkArray1___redArg(v_val_1701_);
v___y_1638_ = v___y_1667_;
v___y_1639_ = v___x_1700_;
v___y_1640_ = v___y_1668_;
v___y_1641_ = v___y_1670_;
v___y_1642_ = v___y_1669_;
v___y_1643_ = v___y_1671_;
v___y_1644_ = v___y_1672_;
v___y_1645_ = v___y_1673_;
v___y_1646_ = v___y_1674_;
v___y_1647_ = v___y_1675_;
v___y_1648_ = v___y_1676_;
v___y_1649_ = v___y_1677_;
v___y_1650_ = v___y_1678_;
v___y_1651_ = v___y_1679_;
v___y_1652_ = v___y_1680_;
v___y_1653_ = v___y_1681_;
v___y_1654_ = v___y_1682_;
v___y_1655_ = v___x_1691_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1685_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1688_;
v___y_1662_ = v___x_1702_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1638_ = v___y_1667_;
v___y_1639_ = v___x_1700_;
v___y_1640_ = v___y_1668_;
v___y_1641_ = v___y_1670_;
v___y_1642_ = v___y_1669_;
v___y_1643_ = v___y_1671_;
v___y_1644_ = v___y_1672_;
v___y_1645_ = v___y_1673_;
v___y_1646_ = v___y_1674_;
v___y_1647_ = v___y_1675_;
v___y_1648_ = v___y_1676_;
v___y_1649_ = v___y_1677_;
v___y_1650_ = v___y_1678_;
v___y_1651_ = v___y_1679_;
v___y_1652_ = v___y_1680_;
v___y_1653_ = v___y_1681_;
v___y_1654_ = v___y_1682_;
v___y_1655_ = v___x_1691_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1685_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1688_;
v___y_1662_ = v___x_1703_;
goto v___jp_1637_;
}
}
v___jp_1704_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_inc_ref(v___y_1724_);
v___x_1727_ = l_Array_append___redArg(v___y_1724_, v___y_1726_);
lean_dec_ref(v___y_1726_);
lean_inc(v___y_1725_);
lean_inc(v___y_1707_);
v___x_1728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1728_, 0, v___y_1707_);
lean_ctor_set(v___x_1728_, 1, v___y_1725_);
lean_ctor_set(v___x_1728_, 2, v___x_1727_);
if (lean_obj_tag(v___y_1715_) == 1)
{
lean_object* v_val_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1729_ = lean_ctor_get(v___y_1715_, 0);
v___x_1730_ = l_Lean_SourceInfo_fromRef(v_val_1729_, v___x_1185_);
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Array_mkArray1___redArg(v___x_1732_);
v___y_1667_ = v___y_1705_;
v___y_1668_ = v___y_1706_;
v___y_1669_ = v___y_1707_;
v___y_1670_ = v___y_1708_;
v___y_1671_ = v___y_1709_;
v___y_1672_ = v___y_1710_;
v___y_1673_ = v___y_1711_;
v___y_1674_ = v___y_1712_;
v___y_1675_ = v___y_1713_;
v___y_1676_ = v___x_1728_;
v___y_1677_ = v___y_1714_;
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1717_;
v___y_1681_ = v___y_1718_;
v___y_1682_ = v___y_1719_;
v___y_1683_ = v___y_1720_;
v___y_1684_ = v___y_1722_;
v___y_1685_ = v___y_1721_;
v___y_1686_ = v___y_1723_;
v___y_1687_ = v___y_1724_;
v___y_1688_ = v___y_1725_;
v___y_1689_ = v___x_1733_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1667_ = v___y_1705_;
v___y_1668_ = v___y_1706_;
v___y_1669_ = v___y_1707_;
v___y_1670_ = v___y_1708_;
v___y_1671_ = v___y_1709_;
v___y_1672_ = v___y_1710_;
v___y_1673_ = v___y_1711_;
v___y_1674_ = v___y_1712_;
v___y_1675_ = v___y_1713_;
v___y_1676_ = v___x_1728_;
v___y_1677_ = v___y_1714_;
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1717_;
v___y_1681_ = v___y_1718_;
v___y_1682_ = v___y_1719_;
v___y_1683_ = v___y_1720_;
v___y_1684_ = v___y_1722_;
v___y_1685_ = v___y_1721_;
v___y_1686_ = v___y_1723_;
v___y_1687_ = v___y_1724_;
v___y_1688_ = v___y_1725_;
v___y_1689_ = v___x_1734_;
goto v___jp_1666_;
}
}
v___jp_1735_:
{
if (lean_obj_tag(v___y_1742_) == 0)
{
lean_object* v_ref_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_ref_1752_ = lean_ctor_get(v___y_1750_, 2);
v___x_1753_ = 0;
v___x_1754_ = l_Lean_SourceInfo_fromRef(v_ref_1752_, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1188_);
lean_inc_ref(v___x_1187_);
lean_inc_ref(v___x_1186_);
v___x_1756_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1755_);
v___x_1757_ = l_Lean_SourceInfo_fromRef(v_tk_1201_, v___x_1185_);
v___x_1758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1755_);
v___x_1759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1760_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1737_) == 1)
{
lean_object* v_val_1761_; lean_object* v___x_1762_; 
v_val_1761_ = lean_ctor_get(v___y_1737_, 0);
lean_inc(v_val_1761_);
v___x_1762_ = l_Array_mkArray1___redArg(v_val_1761_);
v___y_1705_ = v___y_1736_;
v___y_1706_ = v___y_1748_;
v___y_1707_ = v___x_1754_;
v___y_1708_ = v___y_1750_;
v___y_1709_ = v___y_1740_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v_argsArray_1743_;
v___y_1712_ = v___x_1756_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1737_;
v___y_1715_ = v___y_1738_;
v___y_1716_ = v___y_1739_;
v___y_1717_ = v___y_1746_;
v___y_1718_ = v___y_1745_;
v___y_1719_ = v___y_1741_;
v___y_1720_ = v___y_1747_;
v___y_1721_ = v___x_1758_;
v___y_1722_ = v___y_1744_;
v___y_1723_ = v___y_1742_;
v___y_1724_ = v___x_1760_;
v___y_1725_ = v___x_1759_;
v___y_1726_ = v___x_1762_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1705_ = v___y_1736_;
v___y_1706_ = v___y_1748_;
v___y_1707_ = v___x_1754_;
v___y_1708_ = v___y_1750_;
v___y_1709_ = v___y_1740_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v_argsArray_1743_;
v___y_1712_ = v___x_1756_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1737_;
v___y_1715_ = v___y_1738_;
v___y_1716_ = v___y_1739_;
v___y_1717_ = v___y_1746_;
v___y_1718_ = v___y_1745_;
v___y_1719_ = v___y_1741_;
v___y_1720_ = v___y_1747_;
v___y_1721_ = v___x_1758_;
v___y_1722_ = v___y_1744_;
v___y_1723_ = v___y_1742_;
v___y_1724_ = v___x_1760_;
v___y_1725_ = v___x_1759_;
v___y_1726_ = v___x_1763_;
goto v___jp_1704_;
}
}
else
{
lean_object* v_ref_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_ref_1764_ = lean_ctor_get(v___y_1750_, 2);
v___x_1765_ = 0;
v___x_1766_ = l_Lean_SourceInfo_fromRef(v_ref_1764_, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1188_);
lean_inc_ref(v___x_1187_);
lean_inc_ref(v___x_1186_);
v___x_1768_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1767_);
v___x_1769_ = l_Lean_SourceInfo_fromRef(v_tk_1201_, v___x_1185_);
v___x_1770_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1773_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1737_) == 1)
{
lean_object* v_val_1774_; lean_object* v___x_1775_; 
v_val_1774_ = lean_ctor_get(v___y_1737_, 0);
lean_inc(v_val_1774_);
v___x_1775_ = l_Array_mkArray1___redArg(v_val_1774_);
v___y_1607_ = v___y_1736_;
v___y_1608_ = v___x_1771_;
v___y_1609_ = v___x_1772_;
v___y_1610_ = v___y_1748_;
v___y_1611_ = v___y_1750_;
v___y_1612_ = v___x_1773_;
v___y_1613_ = v___y_1740_;
v___y_1614_ = v___y_1749_;
v___y_1615_ = v___x_1768_;
v___y_1616_ = v_argsArray_1743_;
v___y_1617_ = v___y_1751_;
v___y_1618_ = v___y_1737_;
v___y_1619_ = v___y_1738_;
v___y_1620_ = v___y_1739_;
v___y_1621_ = v___y_1746_;
v___y_1622_ = v___y_1745_;
v___y_1623_ = v___y_1741_;
v___y_1624_ = v___y_1747_;
v___y_1625_ = v___y_1744_;
v___y_1626_ = v___y_1742_;
v___y_1627_ = v___x_1766_;
v___y_1628_ = v___x_1775_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1607_ = v___y_1736_;
v___y_1608_ = v___x_1771_;
v___y_1609_ = v___x_1772_;
v___y_1610_ = v___y_1748_;
v___y_1611_ = v___y_1750_;
v___y_1612_ = v___x_1773_;
v___y_1613_ = v___y_1740_;
v___y_1614_ = v___y_1749_;
v___y_1615_ = v___x_1768_;
v___y_1616_ = v_argsArray_1743_;
v___y_1617_ = v___y_1751_;
v___y_1618_ = v___y_1737_;
v___y_1619_ = v___y_1738_;
v___y_1620_ = v___y_1739_;
v___y_1621_ = v___y_1746_;
v___y_1622_ = v___y_1745_;
v___y_1623_ = v___y_1741_;
v___y_1624_ = v___y_1747_;
v___y_1625_ = v___y_1744_;
v___y_1626_ = v___y_1742_;
v___y_1627_ = v___x_1766_;
v___y_1628_ = v___x_1776_;
goto v___jp_1606_;
}
}
}
v___jp_1777_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1785_, v___y_1783_, v___y_1784_, v___y_1781_, v___y_1793_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = l_Lean_LibrarySuggestions_select(v_a_1796_, v___y_1794_, v___y_1783_, v___y_1784_, v___y_1781_, v___y_1793_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; size_t v_sz_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v_sz_1799_ = lean_array_size(v_a_1798_);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1798_, v_sz_1799_, v___x_1800_, v___y_1782_, v___y_1789_, v___y_1785_, v___y_1791_, v___y_1779_, v___y_1783_, v___y_1784_, v___y_1781_, v___y_1793_);
lean_dec(v_a_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___y_1736_ = v___y_1778_;
v___y_1737_ = v___y_1786_;
v___y_1738_ = v___y_1787_;
v___y_1739_ = v___y_1788_;
v___y_1740_ = v___y_1780_;
v___y_1741_ = v___y_1790_;
v___y_1742_ = v___y_1792_;
v_argsArray_1743_ = v_a_1802_;
v___y_1744_ = v___y_1789_;
v___y_1745_ = v___y_1785_;
v___y_1746_ = v___y_1791_;
v___y_1747_ = v___y_1779_;
v___y_1748_ = v___y_1783_;
v___y_1749_ = v___y_1784_;
v___y_1750_ = v___y_1781_;
v___y_1751_ = v___y_1793_;
goto v___jp_1735_;
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v___y_1792_);
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1778_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v_a_1803_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1801_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1801_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v___y_1792_);
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1778_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v_a_1811_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1797_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1797_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1792_);
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1778_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v_a_1819_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1795_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1795_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
v___jp_1827_:
{
lean_object* v_config_1845_; uint8_t v_suggestions_1846_; 
v_config_1845_ = lean_ctor_get(v___y_1840_, 0);
lean_inc_ref(v_config_1845_);
lean_dec_ref(v___y_1840_);
v_suggestions_1846_ = lean_ctor_get_uint8(v_config_1845_, sizeof(void*)*3 + 26);
if (v_suggestions_1846_ == 0)
{
lean_dec_ref(v_config_1845_);
lean_dec_ref(v___f_1189_);
v___y_1736_ = v___y_1828_;
v___y_1737_ = v___y_1835_;
v___y_1738_ = v___y_1836_;
v___y_1739_ = v___y_1837_;
v___y_1740_ = v___y_1830_;
v___y_1741_ = v___y_1839_;
v___y_1742_ = v___y_1842_;
v_argsArray_1743_ = v___y_1844_;
v___y_1744_ = v___y_1838_;
v___y_1745_ = v___y_1834_;
v___y_1746_ = v___y_1841_;
v___y_1747_ = v___y_1829_;
v___y_1748_ = v___y_1832_;
v___y_1749_ = v___y_1833_;
v___y_1750_ = v___y_1831_;
v___y_1751_ = v___y_1843_;
goto v___jp_1735_;
}
else
{
lean_object* v_maxSuggestions_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_maxSuggestions_1847_ = lean_ctor_get(v_config_1845_, 2);
lean_inc(v_maxSuggestions_1847_);
lean_dec_ref(v_config_1845_);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1849_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1847_) == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_unsigned_to_nat(100u);
v___x_1851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1848_);
lean_ctor_set(v___x_1851_, 2, v___f_1189_);
lean_ctor_set(v___x_1851_, 3, v___x_1849_);
v___y_1778_ = v___y_1828_;
v___y_1779_ = v___y_1829_;
v___y_1780_ = v___y_1830_;
v___y_1781_ = v___y_1831_;
v___y_1782_ = v___y_1844_;
v___y_1783_ = v___y_1832_;
v___y_1784_ = v___y_1833_;
v___y_1785_ = v___y_1834_;
v___y_1786_ = v___y_1835_;
v___y_1787_ = v___y_1836_;
v___y_1788_ = v___y_1837_;
v___y_1789_ = v___y_1838_;
v___y_1790_ = v___y_1839_;
v___y_1791_ = v___y_1841_;
v___y_1792_ = v___y_1842_;
v___y_1793_ = v___y_1843_;
v___y_1794_ = v___x_1851_;
goto v___jp_1777_;
}
else
{
lean_object* v_val_1852_; lean_object* v___x_1853_; 
v_val_1852_ = lean_ctor_get(v_maxSuggestions_1847_, 0);
lean_inc(v_val_1852_);
lean_dec_ref_known(v_maxSuggestions_1847_, 1);
v___x_1853_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1853_, 0, v_val_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1848_);
lean_ctor_set(v___x_1853_, 2, v___f_1189_);
lean_ctor_set(v___x_1853_, 3, v___x_1849_);
v___y_1778_ = v___y_1828_;
v___y_1779_ = v___y_1829_;
v___y_1780_ = v___y_1830_;
v___y_1781_ = v___y_1831_;
v___y_1782_ = v___y_1844_;
v___y_1783_ = v___y_1832_;
v___y_1784_ = v___y_1833_;
v___y_1785_ = v___y_1834_;
v___y_1786_ = v___y_1835_;
v___y_1787_ = v___y_1836_;
v___y_1788_ = v___y_1837_;
v___y_1789_ = v___y_1838_;
v___y_1790_ = v___y_1839_;
v___y_1791_ = v___y_1841_;
v___y_1792_ = v___y_1842_;
v___y_1793_ = v___y_1843_;
v___y_1794_ = v___x_1853_;
goto v___jp_1777_;
}
}
}
v___jp_1854_:
{
uint8_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = 0;
lean_inc(v___y_1865_);
v___x_1870_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1865_, v___x_1869_, v___y_1867_, v___y_1859_, v___y_1861_);
if (lean_obj_tag(v___x_1870_) == 0)
{
if (lean_obj_tag(v___y_1864_) == 1)
{
lean_object* v_a_1871_; lean_object* v_val_1872_; lean_object* v___x_1873_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v_val_1872_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v___y_1864_, 1);
v___x_1873_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1872_);
lean_dec(v_val_1872_);
lean_inc(v___y_1855_);
v___y_1828_ = v___y_1855_;
v___y_1829_ = v___y_1857_;
v___y_1830_ = v___x_1869_;
v___y_1831_ = v___y_1859_;
v___y_1832_ = v___y_1862_;
v___y_1833_ = v___y_1856_;
v___y_1834_ = v___y_1863_;
v___y_1835_ = v___y_1868_;
v___y_1836_ = v___y_1866_;
v___y_1837_ = v___y_1855_;
v___y_1838_ = v___y_1867_;
v___y_1839_ = v___y_1865_;
v___y_1840_ = v_a_1871_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___y_1861_;
v___y_1844_ = v___x_1873_;
goto v___jp_1827_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1875_; 
lean_dec(v___y_1864_);
v_a_1874_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1855_);
v___y_1828_ = v___y_1855_;
v___y_1829_ = v___y_1857_;
v___y_1830_ = v___x_1869_;
v___y_1831_ = v___y_1859_;
v___y_1832_ = v___y_1862_;
v___y_1833_ = v___y_1856_;
v___y_1834_ = v___y_1863_;
v___y_1835_ = v___y_1868_;
v___y_1836_ = v___y_1866_;
v___y_1837_ = v___y_1855_;
v___y_1838_ = v___y_1867_;
v___y_1839_ = v___y_1865_;
v___y_1840_ = v_a_1874_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___y_1861_;
v___y_1844_ = v___x_1875_;
goto v___jp_1827_;
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v___y_1868_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1858_);
lean_dec(v___y_1855_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v_a_1876_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1870_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1870_);
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
v___jp_1884_:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Syntax_getOptional_x3f(v___y_1889_);
lean_dec(v___y_1889_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_box(0);
v___y_1855_ = v___y_1898_;
v___y_1856_ = v___y_1890_;
v___y_1857_ = v___y_1885_;
v___y_1858_ = v___y_1896_;
v___y_1859_ = v___y_1887_;
v___y_1860_ = v___y_1895_;
v___y_1861_ = v___y_1897_;
v___y_1862_ = v___y_1888_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1886_;
v___y_1865_ = v___y_1894_;
v___y_1866_ = v___y_1892_;
v___y_1867_ = v___y_1893_;
v___y_1868_ = v___x_1900_;
goto v___jp_1854_;
}
else
{
lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_val_1901_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1899_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_dec(v___x_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1855_ = v___y_1898_;
v___y_1856_ = v___y_1890_;
v___y_1857_ = v___y_1885_;
v___y_1858_ = v___y_1896_;
v___y_1859_ = v___y_1887_;
v___y_1860_ = v___y_1895_;
v___y_1861_ = v___y_1897_;
v___y_1862_ = v___y_1888_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1886_;
v___y_1865_ = v___y_1894_;
v___y_1866_ = v___y_1892_;
v___y_1867_ = v___y_1893_;
v___y_1868_ = v___x_1906_;
goto v___jp_1854_;
}
}
}
}
v___jp_1909_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_unsigned_to_nat(4u);
v___x_1925_ = l_Lean_Syntax_getArg(v___y_1913_, v___x_1924_);
lean_dec(v___y_1913_);
v___x_1926_ = l_Lean_Syntax_getOptional_x3f(v___x_1925_);
lean_dec(v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_box(0);
v___y_1885_ = v___y_1919_;
v___y_1886_ = v_args_1915_;
v___y_1887_ = v___y_1922_;
v___y_1888_ = v___y_1920_;
v___y_1889_ = v___y_1912_;
v___y_1890_ = v___y_1921_;
v___y_1891_ = v___y_1917_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1918_;
v___y_1896_ = v___y_1914_;
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___x_1927_;
goto v___jp_1884_;
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_val_1928_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1926_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_val_1928_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_val_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v___y_1885_ = v___y_1919_;
v___y_1886_ = v_args_1915_;
v___y_1887_ = v___y_1922_;
v___y_1888_ = v___y_1920_;
v___y_1889_ = v___y_1912_;
v___y_1890_ = v___y_1921_;
v___y_1891_ = v___y_1917_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1918_;
v___y_1896_ = v___y_1914_;
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___x_1933_;
goto v___jp_1884_;
}
}
}
}
v___jp_1937_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1951_ = lean_unsigned_to_nat(3u);
v___x_1952_ = l_Lean_Syntax_getArg(v___y_1940_, v___x_1951_);
v___x_1953_ = l_Lean_Syntax_isNone(v___x_1952_);
if (v___x_1953_ == 0)
{
uint8_t v___x_1954_; 
lean_inc(v___x_1952_);
v___x_1954_ = l_Lean_Syntax_matchesNull(v___x_1952_, v___x_1936_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec(v___x_1952_);
lean_dec(v_o_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1956_ = l_Lean_Syntax_getArg(v___x_1952_, v___x_1200_);
lean_dec(v___x_1952_);
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1188_);
lean_inc_ref(v___x_1187_);
lean_inc_ref(v___x_1186_);
v___x_1958_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1957_);
lean_inc(v___x_1956_);
v___x_1959_ = l_Lean_Syntax_isOfKind(v___x_1956_, v___x_1958_);
lean_dec(v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec(v___x_1956_);
lean_dec(v_o_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v_args_1962_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_Syntax_getArg(v___x_1956_, v___x_1936_);
lean_dec(v___x_1956_);
v_args_1962_ = l_Lean_Syntax_getArgs(v___x_1961_);
lean_dec(v___x_1961_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_args_1962_);
v___y_1910_ = v_o_1942_;
v___y_1911_ = v___y_1938_;
v___y_1912_ = v___y_1939_;
v___y_1913_ = v___y_1940_;
v___y_1914_ = v___y_1941_;
v_args_1915_ = v___x_1963_;
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v___y_1946_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1949_;
v___y_1923_ = v___y_1950_;
goto v___jp_1909_;
}
}
}
else
{
lean_object* v___x_1964_; 
lean_dec(v___x_1952_);
v___x_1964_ = lean_box(0);
v___y_1910_ = v_o_1942_;
v___y_1911_ = v___y_1938_;
v___y_1912_ = v___y_1939_;
v___y_1913_ = v___y_1940_;
v___y_1914_ = v___y_1941_;
v_args_1915_ = v___x_1964_;
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v___y_1946_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1949_;
v___y_1923_ = v___y_1950_;
goto v___jp_1909_;
}
}
v___jp_1965_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1975_ = lean_unsigned_to_nat(2u);
v___x_1976_ = l_Lean_Syntax_getArg(v_stx_1184_, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1188_);
lean_inc_ref(v___x_1187_);
lean_inc_ref(v___x_1186_);
v___x_1978_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1977_);
lean_inc(v___x_1976_);
v___x_1979_ = l_Lean_Syntax_isOfKind(v___x_1976_, v___x_1978_);
lean_dec(v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v___x_1976_);
lean_dec(v_bang_1966_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1980_;
}
else
{
lean_object* v_cfg_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_cfg_1981_ = l_Lean_Syntax_getArg(v___x_1976_, v___x_1200_);
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1188_);
lean_inc_ref(v___x_1187_);
lean_inc_ref(v___x_1186_);
v___x_1983_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1982_);
lean_inc(v_cfg_1981_);
v___x_1984_ = l_Lean_Syntax_isOfKind(v_cfg_1981_, v___x_1983_);
lean_dec(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v_cfg_1981_);
lean_dec(v___x_1976_);
lean_dec(v_bang_1966_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = l_Lean_Syntax_getArg(v___x_1976_, v___x_1936_);
v___x_1987_ = l_Lean_Syntax_getArg(v___x_1976_, v___x_1975_);
v___x_1988_ = l_Lean_Syntax_isNone(v___x_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
lean_inc(v___x_1987_);
v___x_1989_ = l_Lean_Syntax_matchesNull(v___x_1987_, v___x_1936_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec(v___x_1987_);
lean_dec(v___x_1986_);
lean_dec(v_cfg_1981_);
lean_dec(v___x_1976_);
lean_dec(v_bang_1966_);
lean_dec(v_tk_1201_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v___x_1990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1990_;
}
else
{
lean_object* v_o_1991_; lean_object* v___x_1992_; 
v_o_1991_ = l_Lean_Syntax_getArg(v___x_1987_, v___x_1200_);
lean_dec(v___x_1987_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_o_1991_);
v___y_1938_ = v_cfg_1981_;
v___y_1939_ = v___x_1986_;
v___y_1940_ = v___x_1976_;
v___y_1941_ = v_bang_1966_;
v_o_1942_ = v___x_1992_;
v___y_1943_ = v___y_1967_;
v___y_1944_ = v___y_1968_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1971_;
v___y_1948_ = v___y_1972_;
v___y_1949_ = v___y_1973_;
v___y_1950_ = v___y_1974_;
goto v___jp_1937_;
}
}
else
{
lean_object* v___x_1993_; 
lean_dec(v___x_1987_);
v___x_1993_ = lean_box(0);
v___y_1938_ = v_cfg_1981_;
v___y_1939_ = v___x_1986_;
v___y_1940_ = v___x_1976_;
v___y_1941_ = v_bang_1966_;
v_o_1942_ = v___x_1993_;
v___y_1943_ = v___y_1967_;
v___y_1944_ = v___y_1968_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1971_;
v___y_1948_ = v___y_1972_;
v___y_1949_ = v___y_1973_;
v___y_1950_ = v___y_1974_;
goto v___jp_1937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2001_, lean_object* v_stx_2002_, lean_object* v___x_2003_, lean_object* v___x_2004_, lean_object* v___x_2005_, lean_object* v___x_2006_, lean_object* v___f_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v___x_35162__boxed_2017_; uint8_t v___x_35163__boxed_2018_; lean_object* v_res_2019_; 
v___x_35162__boxed_2017_ = lean_unbox(v___x_2001_);
v___x_35163__boxed_2018_ = lean_unbox(v___x_2003_);
v_res_2019_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35162__boxed_2017_, v_stx_2002_, v___x_35163__boxed_2018_, v___x_2004_, v___x_2005_, v___x_2006_, v___f_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v_stx_2002_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; uint8_t v___x_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___y_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2042_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2029_);
v___x_2043_ = l_Lean_Syntax_isOfKind(v_stx_2029_, v___x_2042_);
v___x_2044_ = 1;
v___f_2045_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2046_ = lean_box(v___x_2043_);
v___x_2047_ = lean_box(v___x_2044_);
v___y_2048_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2048_, 0, v___x_2046_);
lean_closure_set(v___y_2048_, 1, v_stx_2029_);
lean_closure_set(v___y_2048_, 2, v___x_2047_);
lean_closure_set(v___y_2048_, 3, v___x_2039_);
lean_closure_set(v___y_2048_, 4, v___x_2040_);
lean_closure_set(v___y_2048_, 5, v___x_2041_);
lean_closure_set(v___y_2048_, 6, v___f_2045_);
v___x_2049_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2049_, 0, v___y_2048_);
v___x_2050_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2049_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2062_, lean_object* v_as_2063_, lean_object* v_as_x27_2064_, lean_object* v_b_2065_, lean_object* v_a_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2062_, v_as_x27_2064_, v_b_2065_, v___y_2073_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2077_, lean_object* v_as_2078_, lean_object* v_as_x27_2079_, lean_object* v_b_2080_, lean_object* v_a_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2077_, v_as_2078_, v_as_x27_2079_, v_b_2080_, v_a_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v_as_x27_2079_);
lean_dec(v_as_2078_);
lean_dec(v___x_2077_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2092_, lean_object* v_ref_2093_, lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2093_, v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_ref_2106_, lean_object* v_msg_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2105_, v_ref_2106_, v_msg_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_ref_2106_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2118_, lean_object* v_ref_2119_, lean_object* v_constName_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2119_, v_constName_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2131_, lean_object* v_ref_2132_, lean_object* v_constName_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2131_, v_ref_2132_, v_constName_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v_ref_2132_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2145_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_msg_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2156_, v_msg_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2168_, v___y_2175_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_opt_2179_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2190_, lean_object* v_ref_2191_, lean_object* v_msg_2192_, lean_object* v_declHint_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2191_, v_msg_2192_, v_declHint_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_ref_2205_, lean_object* v_msg_2206_, lean_object* v_declHint_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2204_, v_ref_2205_, v_msg_2206_, v_declHint_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v_ref_2205_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2218_, lean_object* v_declHint_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2218_, v_declHint_2219_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2230_, lean_object* v_declHint_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2230_, v_declHint_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2242_, lean_object* v_msgData_2243_, uint8_t v_severity_2244_, uint8_t v_isSilent_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2242_, v_msgData_2243_, v_severity_2244_, v_isSilent_2245_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2256_, lean_object* v_msgData_2257_, lean_object* v_severity_2258_, lean_object* v_isSilent_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_severity_boxed_2269_; uint8_t v_isSilent_boxed_2270_; lean_object* v_res_2271_; 
v_severity_boxed_2269_ = lean_unbox(v_severity_2258_);
v_isSilent_boxed_2270_ = lean_unbox(v_isSilent_2259_);
v_res_2271_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2256_, v_msgData_2257_, v_severity_boxed_2269_, v_isSilent_boxed_2270_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v_ref_2256_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2279_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2282_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2283_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2314_ = l_Lean_addBuiltinDeclarationRanges(v___x_2312_, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2317_, lean_object* v_as_x27_2318_, lean_object* v_b_2319_, lean_object* v___y_2320_){
_start:
{
if (lean_obj_tag(v_as_x27_2318_) == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_b_2319_);
return v___x_2322_;
}
else
{
lean_object* v_head_2323_; lean_object* v_tail_2324_; lean_object* v_ref_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_head_2323_ = lean_ctor_get(v_as_x27_2318_, 0);
v_tail_2324_ = lean_ctor_get(v_as_x27_2318_, 1);
v_ref_2325_ = lean_ctor_get(v___y_2320_, 2);
v___x_2326_ = 1;
v___x_2327_ = 0;
v___x_2328_ = l_Lean_SourceInfo_fromRef(v_ref_2325_, v___x_2327_);
v___x_2329_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2330_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2331_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2328_);
v___x_2332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2330_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
lean_inc(v_head_2323_);
v___x_2333_ = l_Lean_mkCIdentFrom(v___x_2317_, v_head_2323_, v___x_2326_);
lean_inc_ref(v___x_2332_);
v___x_2334_ = l_Lean_Syntax_node3(v___x_2328_, v___x_2329_, v___x_2332_, v___x_2332_, v___x_2333_);
v___x_2335_ = lean_array_push(v_b_2319_, v___x_2334_);
v_as_x27_2318_ = v_tail_2324_;
v_b_2319_ = v___x_2335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2337_, lean_object* v_as_x27_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2337_, v_as_x27_2338_, v_b_2339_, v___y_2340_);
lean_dec_ref(v___y_2340_);
lean_dec(v_as_x27_2338_);
lean_dec(v___x_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2343_, size_t v_sz_2344_, size_t v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_usize_dec_lt(v_i_2345_, v_sz_2344_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_b_2346_);
return v___x_2357_;
}
else
{
lean_object* v_a_2358_; lean_object* v_name_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2358_ = lean_array_uget_borrowed(v_as_2343_, v_i_2345_);
v_name_2359_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_name_2359_);
v___x_2360_ = l_Lean_mkIdent(v_name_2359_);
lean_inc(v___x_2360_);
v___x_2361_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2360_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2360_, v_a_2362_, v_b_2346_, v___y_2353_);
lean_dec(v_a_2362_);
lean_dec(v___x_2360_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; size_t v___x_2365_; size_t v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2345_, v___x_2365_);
v_i_2345_ = v___x_2366_;
v_b_2346_ = v_a_2364_;
goto _start;
}
else
{
return v___x_2363_;
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v___x_2360_);
lean_dec_ref(v_b_2346_);
v_a_2368_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2361_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2361_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2376_, lean_object* v_sz_2377_, lean_object* v_i_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
size_t v_sz_boxed_2389_; size_t v_i_boxed_2390_; lean_object* v_res_2391_; 
v_sz_boxed_2389_ = lean_unbox_usize(v_sz_2377_);
lean_dec(v_sz_2377_);
v_i_boxed_2390_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2376_, v_sz_boxed_2389_, v_i_boxed_2390_, v_b_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v_as_2376_);
return v_res_2391_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2394_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_unsigned_to_nat(32u);
v___x_2398_ = lean_mk_empty_array_with_capacity(v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = ((size_t)5ULL);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_unsigned_to_nat(32u);
v___x_2403_ = lean_mk_empty_array_with_capacity(v___x_2402_);
v___x_2404_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2405_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2403_);
lean_ctor_set(v___x_2405_, 2, v___x_2401_);
lean_ctor_set(v___x_2405_, 3, v___x_2401_);
lean_ctor_set_usize(v___x_2405_, 4, v___x_2400_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2407_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
lean_ctor_set(v___x_2408_, 2, v___x_2407_);
lean_ctor_set(v___x_2408_, 3, v___x_2406_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2410_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2420_, lean_object* v_stx_2421_, uint8_t v___x_2422_, lean_object* v___x_2423_, lean_object* v___x_2424_, lean_object* v___x_2425_, lean_object* v___f_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
if (v___x_2420_ == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_2436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; lean_object* v_tk_2438_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2553_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v_stxForSuggestion_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; uint8_t v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; uint8_t v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; uint8_t v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v_stxForExecution_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; uint8_t v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; uint8_t v___y_3120_; lean_object* v_argsArray_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v_args_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___x_3308_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v_o_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v_bang_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_2437_ = lean_unsigned_to_nat(0u);
v_tk_2438_ = l_Lean_Syntax_getArg(v_stx_2421_, v___x_2437_);
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3366_ = l_Lean_Syntax_getArg(v_stx_2421_, v___x_3308_);
v___x_3367_ = l_Lean_Syntax_isNone(v___x_3366_);
if (v___x_3367_ == 0)
{
uint8_t v___x_3368_; 
lean_inc(v___x_3366_);
v___x_3368_ = l_Lean_Syntax_matchesNull(v___x_3366_, v___x_3308_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; 
lean_dec(v___x_3366_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3369_;
}
else
{
lean_object* v_bang_3370_; lean_object* v___x_3371_; 
v_bang_3370_ = l_Lean_Syntax_getArg(v___x_3366_, v___x_2437_);
lean_dec(v___x_3366_);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v_bang_3370_);
v_bang_3338_ = v___x_3371_;
v___y_3339_ = v___y_2427_;
v___y_3340_ = v___y_2428_;
v___y_3341_ = v___y_2429_;
v___y_3342_ = v___y_2430_;
v___y_3343_ = v___y_2431_;
v___y_3344_ = v___y_2432_;
v___y_3345_ = v___y_2433_;
v___y_3346_ = v___y_2434_;
goto v___jp_3337_;
}
}
else
{
lean_object* v___x_3372_; 
lean_dec(v___x_3366_);
v___x_3372_ = lean_box(0);
v_bang_3338_ = v___x_3372_;
v___y_3339_ = v___y_2427_;
v___y_3340_ = v___y_2428_;
v___y_3341_ = v___y_2429_;
v___y_3342_ = v___y_2430_;
v___y_3343_ = v___y_2431_;
v___y_3344_ = v___y_2432_;
v___y_3345_ = v___y_2433_;
v___y_3346_ = v___y_2434_;
goto v___jp_3337_;
}
v___jp_2439_:
{
lean_object* v_usedTheorems_2446_; lean_object* v_diag_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2489_; 
v_usedTheorems_2446_ = lean_ctor_get(v___y_2440_, 0);
v_diag_2447_ = lean_ctor_get(v___y_2440_, 1);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___y_2440_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2449_ = v___y_2440_;
v_isShared_2450_ = v_isSharedCheck_2489_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_diag_2447_);
lean_inc(v_usedTheorems_2446_);
lean_dec(v___y_2440_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2489_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2441_, v_usedTheorems_2446_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec_ref(v_usedTheorems_2446_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v_ref_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_ref_2453_ = lean_ctor_get(v___y_2444_, 2);
v___x_2454_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_a_2452_);
lean_ctor_set(v___x_2449_, 0, v___x_2454_);
v___x_2456_ = v___x_2449_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_a_2452_);
v___x_2456_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
lean_ctor_set(v___x_2458_, 3, v___x_2457_);
lean_ctor_set(v___x_2458_, 4, v___x_2457_);
lean_ctor_set(v___x_2458_, 5, v___x_2457_);
lean_inc(v_ref_2453_);
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_ref_2453_);
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2461_ = 4;
v___x_2462_ = l_Lean_MessageData_nil;
v___x_2463_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2438_, v___x_2458_, v___x_2459_, v___x_2460_, v___x_2457_, v___x_2461_, v___x_2462_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2463_, 0);
lean_dec(v_unused_2471_);
v___x_2465_ = v___x_2463_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v___x_2463_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v_diag_2447_);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_diag_2447_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_diag_2447_);
v_a_2472_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2463_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2463_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_del_object(v___x_2449_);
lean_dec_ref(v_diag_2447_);
lean_dec(v_tk_2438_);
v_a_2481_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2451_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2451_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
v___jp_2490_:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2497_, v___y_2492_, v___y_2491_, v___y_2494_, v___y_2496_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2502_ = l_Lean_Meta_simpAll(v_a_2500_, v___y_2498_, v___y_2493_, v___x_2501_, v___y_2492_, v___y_2491_, v___y_2494_, v___y_2496_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v_fst_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v_fst_2504_ = lean_ctor_get(v_a_2503_, 0);
if (lean_obj_tag(v_fst_2504_) == 0)
{
lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_snd_2505_ = lean_ctor_get(v_a_2503_, 1);
lean_inc(v_snd_2505_);
lean_dec(v_a_2503_);
v___x_2506_ = lean_box(0);
v___x_2507_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2506_, v___y_2497_, v___y_2492_, v___y_2491_, v___y_2494_, v___y_2496_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_dec_ref_known(v___x_2507_, 1);
v___y_2440_ = v_snd_2505_;
v___y_2441_ = v___y_2495_;
v___y_2442_ = v___y_2492_;
v___y_2443_ = v___y_2491_;
v___y_2444_ = v___y_2494_;
v___y_2445_ = v___y_2496_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_snd_2505_);
lean_dec(v___y_2495_);
lean_dec(v_tk_2438_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_snd_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2534_; 
lean_inc_ref(v_fst_2504_);
v_snd_2516_ = lean_ctor_get(v_a_2503_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_a_2503_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v_a_2503_, 0);
lean_dec(v_unused_2535_);
v___x_2518_ = v_a_2503_;
v_isShared_2519_ = v_isSharedCheck_2534_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_snd_2516_);
lean_dec(v_a_2503_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2534_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_val_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v_val_2520_ = lean_ctor_get(v_fst_2504_, 0);
lean_inc(v_val_2520_);
lean_dec_ref_known(v_fst_2504_, 1);
v___x_2521_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
lean_ctor_set(v___x_2518_, 1, v___x_2521_);
lean_ctor_set(v___x_2518_, 0, v_val_2520_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_val_2520_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2523_, v___y_2497_, v___y_2492_, v___y_2491_, v___y_2494_, v___y_2496_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref_known(v___x_2524_, 1);
v___y_2440_ = v_snd_2516_;
v___y_2441_ = v___y_2495_;
v___y_2442_ = v___y_2492_;
v___y_2443_ = v___y_2491_;
v___y_2444_ = v___y_2494_;
v___y_2445_ = v___y_2496_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_snd_2516_);
lean_dec(v___y_2495_);
lean_dec(v_tk_2438_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v___y_2495_);
lean_dec(v_tk_2438_);
v_a_2536_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2502_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2502_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2493_);
lean_dec(v_tk_2438_);
v_a_2544_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2499_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2499_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
v___jp_2552_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2566_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2553_, v___x_2422_, v___y_2555_, v___x_2422_, v___x_2565_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2553_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
if (lean_obj_tag(v___y_2554_) == 0)
{
lean_object* v_ctx_2568_; lean_object* v_simprocs_2569_; 
v_ctx_2568_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_ref(v_ctx_2568_);
v_simprocs_2569_ = lean_ctor_get(v_a_2567_, 1);
lean_inc_ref(v_simprocs_2569_);
lean_dec(v_a_2567_);
v___y_2491_ = v___y_2562_;
v___y_2492_ = v___y_2561_;
v___y_2493_ = v_simprocs_2569_;
v___y_2494_ = v___y_2563_;
v___y_2495_ = v_stxForSuggestion_2556_;
v___y_2496_ = v___y_2564_;
v___y_2497_ = v___y_2558_;
v___y_2498_ = v_ctx_2568_;
goto v___jp_2490_;
}
else
{
lean_object* v_ctx_2570_; lean_object* v_simprocs_2571_; lean_object* v___x_2572_; 
lean_dec_ref_known(v___y_2554_, 1);
v_ctx_2570_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_ref(v_ctx_2570_);
v_simprocs_2571_ = lean_ctor_get(v_a_2567_, 1);
lean_inc_ref(v_simprocs_2571_);
lean_dec(v_a_2567_);
v___x_2572_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2570_);
v___y_2491_ = v___y_2562_;
v___y_2492_ = v___y_2561_;
v___y_2493_ = v_simprocs_2571_;
v___y_2494_ = v___y_2563_;
v___y_2495_ = v_stxForSuggestion_2556_;
v___y_2496_ = v___y_2564_;
v___y_2497_ = v___y_2558_;
v___y_2498_ = v___x_2572_;
goto v___jp_2490_;
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_stxForSuggestion_2556_);
lean_dec(v___y_2554_);
lean_dec(v_tk_2438_);
v_a_2573_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2566_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2566_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
v___jp_2581_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_inc_ref_n(v___y_2599_, 2);
v___x_2602_ = l_Array_append___redArg(v___y_2599_, v___y_2601_);
lean_dec_ref(v___y_2601_);
lean_inc_n(v___y_2597_, 3);
lean_inc_n(v___y_2589_, 5);
v___x_2603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2603_, 0, v___y_2589_);
lean_ctor_set(v___x_2603_, 1, v___y_2597_);
lean_ctor_set(v___x_2603_, 2, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___y_2589_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2607_ = l_Lean_Syntax_SepArray_ofElems(v___x_2606_, v___y_2592_);
lean_dec_ref(v___y_2592_);
v___x_2608_ = l_Array_append___redArg(v___y_2599_, v___x_2607_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2609_, 0, v___y_2589_);
lean_ctor_set(v___x_2609_, 1, v___y_2597_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2589_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node3(v___y_2589_, v___y_2597_, v___x_2605_, v___x_2609_, v___x_2611_);
v___x_2613_ = l_Lean_Syntax_node5(v___y_2589_, v___y_2598_, v___y_2596_, v___y_2600_, v___y_2593_, v___x_2603_, v___x_2612_);
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2585_;
v___y_2555_ = v___y_2591_;
v_stxForSuggestion_2556_ = v___x_2613_;
v___y_2557_ = v___y_2587_;
v___y_2558_ = v___y_2583_;
v___y_2559_ = v___y_2590_;
v___y_2560_ = v___y_2594_;
v___y_2561_ = v___y_2588_;
v___y_2562_ = v___y_2595_;
v___y_2563_ = v___y_2586_;
v___y_2564_ = v___y_2584_;
goto v___jp_2552_;
}
v___jp_2614_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_inc_ref(v___y_2633_);
v___x_2635_ = l_Array_append___redArg(v___y_2633_, v___y_2634_);
lean_dec_ref(v___y_2634_);
lean_inc(v___y_2631_);
lean_inc(v___y_2623_);
v___x_2636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2623_);
lean_ctor_set(v___x_2636_, 1, v___y_2631_);
lean_ctor_set(v___x_2636_, 2, v___x_2635_);
if (lean_obj_tag(v___y_2618_) == 1)
{
lean_object* v_val_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_val_2637_ = lean_ctor_get(v___y_2618_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v___y_2618_, 1);
v___x_2638_ = l_Lean_SourceInfo_fromRef(v_val_2637_, v___x_2422_);
lean_dec(v_val_2637_);
v___x_2639_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Array_mkArray1___redArg(v___x_2640_);
v___y_2582_ = v___y_2615_;
v___y_2583_ = v___y_2616_;
v___y_2584_ = v___y_2617_;
v___y_2585_ = v___y_2619_;
v___y_2586_ = v___y_2620_;
v___y_2587_ = v___y_2621_;
v___y_2588_ = v___y_2622_;
v___y_2589_ = v___y_2623_;
v___y_2590_ = v___y_2624_;
v___y_2591_ = v___y_2625_;
v___y_2592_ = v___y_2626_;
v___y_2593_ = v___x_2636_;
v___y_2594_ = v___y_2627_;
v___y_2595_ = v___y_2629_;
v___y_2596_ = v___y_2628_;
v___y_2597_ = v___y_2631_;
v___y_2598_ = v___y_2630_;
v___y_2599_ = v___y_2633_;
v___y_2600_ = v___y_2632_;
v___y_2601_ = v___x_2641_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2642_; 
lean_dec(v___y_2618_);
v___x_2642_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2582_ = v___y_2615_;
v___y_2583_ = v___y_2616_;
v___y_2584_ = v___y_2617_;
v___y_2585_ = v___y_2619_;
v___y_2586_ = v___y_2620_;
v___y_2587_ = v___y_2621_;
v___y_2588_ = v___y_2622_;
v___y_2589_ = v___y_2623_;
v___y_2590_ = v___y_2624_;
v___y_2591_ = v___y_2625_;
v___y_2592_ = v___y_2626_;
v___y_2593_ = v___x_2636_;
v___y_2594_ = v___y_2627_;
v___y_2595_ = v___y_2629_;
v___y_2596_ = v___y_2628_;
v___y_2597_ = v___y_2631_;
v___y_2598_ = v___y_2630_;
v___y_2599_ = v___y_2633_;
v___y_2600_ = v___y_2632_;
v___y_2601_ = v___x_2642_;
goto v___jp_2581_;
}
}
v___jp_2643_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_inc_ref_n(v___y_2645_, 2);
v___x_2664_ = l_Array_append___redArg(v___y_2645_, v___y_2663_);
lean_dec_ref(v___y_2663_);
lean_inc_n(v___y_2662_, 3);
lean_inc_n(v___y_2646_, 5);
v___x_2665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___y_2646_);
lean_ctor_set(v___x_2665_, 1, v___y_2662_);
lean_ctor_set(v___x_2665_, 2, v___x_2664_);
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2646_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2669_ = l_Lean_Syntax_SepArray_ofElems(v___x_2668_, v___y_2657_);
lean_dec_ref(v___y_2657_);
v___x_2670_ = l_Array_append___redArg(v___y_2645_, v___x_2669_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2646_);
lean_ctor_set(v___x_2671_, 1, v___y_2662_);
lean_ctor_set(v___x_2671_, 2, v___x_2670_);
v___x_2672_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2646_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_Syntax_node3(v___y_2646_, v___y_2662_, v___x_2667_, v___x_2671_, v___x_2673_);
v___x_2675_ = l_Lean_Syntax_node5(v___y_2646_, v___y_2654_, v___y_2658_, v___y_2661_, v___y_2652_, v___x_2665_, v___x_2674_);
v___y_2553_ = v___y_2644_;
v___y_2554_ = v___y_2649_;
v___y_2555_ = v___y_2656_;
v_stxForSuggestion_2556_ = v___x_2675_;
v___y_2557_ = v___y_2651_;
v___y_2558_ = v___y_2647_;
v___y_2559_ = v___y_2655_;
v___y_2560_ = v___y_2659_;
v___y_2561_ = v___y_2653_;
v___y_2562_ = v___y_2660_;
v___y_2563_ = v___y_2650_;
v___y_2564_ = v___y_2648_;
goto v___jp_2552_;
}
v___jp_2676_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc_ref(v___y_2677_);
v___x_2697_ = l_Array_append___redArg(v___y_2677_, v___y_2696_);
lean_dec_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2678_);
v___x_2698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2698_, 0, v___y_2678_);
lean_ctor_set(v___x_2698_, 1, v___y_2695_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
if (lean_obj_tag(v___y_2682_) == 1)
{
lean_object* v_val_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_val_2699_ = lean_ctor_get(v___y_2682_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v___y_2682_, 1);
v___x_2700_ = l_Lean_SourceInfo_fromRef(v_val_2699_, v___x_2422_);
lean_dec(v_val_2699_);
v___x_2701_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Array_mkArray1___redArg(v___x_2702_);
v___y_2644_ = v___y_2679_;
v___y_2645_ = v___y_2677_;
v___y_2646_ = v___y_2678_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v___y_2683_;
v___y_2650_ = v___y_2684_;
v___y_2651_ = v___y_2685_;
v___y_2652_ = v___x_2698_;
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___y_2688_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2690_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2693_;
v___y_2661_ = v___y_2694_;
v___y_2662_ = v___y_2695_;
v___y_2663_ = v___x_2703_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2704_; 
lean_dec(v___y_2682_);
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2644_ = v___y_2679_;
v___y_2645_ = v___y_2677_;
v___y_2646_ = v___y_2678_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v___y_2683_;
v___y_2650_ = v___y_2684_;
v___y_2651_ = v___y_2685_;
v___y_2652_ = v___x_2698_;
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___y_2688_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2690_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2693_;
v___y_2661_ = v___y_2694_;
v___y_2662_ = v___y_2695_;
v___y_2663_ = v___x_2704_;
goto v___jp_2643_;
}
}
v___jp_2705_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_inc_ref_n(v___y_2709_, 2);
v___x_2725_ = l_Array_append___redArg(v___y_2709_, v___y_2724_);
lean_dec_ref(v___y_2724_);
lean_inc_n(v___y_2715_, 2);
lean_inc_n(v___y_2717_, 2);
v___x_2726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2726_, 0, v___y_2717_);
lean_ctor_set(v___x_2726_, 1, v___y_2715_);
lean_ctor_set(v___x_2726_, 2, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2727_, 0, v___y_2717_);
lean_ctor_set(v___x_2727_, 1, v___y_2715_);
lean_ctor_set(v___x_2727_, 2, v___y_2709_);
v___x_2728_ = l_Lean_Syntax_node5(v___y_2717_, v___y_2714_, v___y_2722_, v___y_2723_, v___y_2721_, v___x_2726_, v___x_2727_);
v___y_2553_ = v___y_2706_;
v___y_2554_ = v___y_2710_;
v___y_2555_ = v___y_2718_;
v_stxForSuggestion_2556_ = v___x_2728_;
v___y_2557_ = v___y_2712_;
v___y_2558_ = v___y_2707_;
v___y_2559_ = v___y_2716_;
v___y_2560_ = v___y_2719_;
v___y_2561_ = v___y_2713_;
v___y_2562_ = v___y_2720_;
v___y_2563_ = v___y_2711_;
v___y_2564_ = v___y_2708_;
goto v___jp_2552_;
}
v___jp_2729_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_inc_ref(v___y_2734_);
v___x_2749_ = l_Array_append___redArg(v___y_2734_, v___y_2748_);
lean_dec_ref(v___y_2748_);
lean_inc(v___y_2740_);
lean_inc(v___y_2742_);
v___x_2750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2742_);
lean_ctor_set(v___x_2750_, 1, v___y_2740_);
lean_ctor_set(v___x_2750_, 2, v___x_2749_);
if (lean_obj_tag(v___y_2733_) == 1)
{
lean_object* v_val_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_val_2751_ = lean_ctor_get(v___y_2733_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v___y_2733_, 1);
v___x_2752_ = l_Lean_SourceInfo_fromRef(v_val_2751_, v___x_2422_);
lean_dec(v_val_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Array_mkArray1___redArg(v___x_2754_);
v___y_2706_ = v___y_2730_;
v___y_2707_ = v___y_2731_;
v___y_2708_ = v___y_2732_;
v___y_2709_ = v___y_2734_;
v___y_2710_ = v___y_2735_;
v___y_2711_ = v___y_2736_;
v___y_2712_ = v___y_2737_;
v___y_2713_ = v___y_2738_;
v___y_2714_ = v___y_2739_;
v___y_2715_ = v___y_2740_;
v___y_2716_ = v___y_2741_;
v___y_2717_ = v___y_2742_;
v___y_2718_ = v___y_2743_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___y_2745_;
v___y_2721_ = v___x_2750_;
v___y_2722_ = v___y_2746_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___x_2755_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2756_; 
lean_dec(v___y_2733_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2706_ = v___y_2730_;
v___y_2707_ = v___y_2731_;
v___y_2708_ = v___y_2732_;
v___y_2709_ = v___y_2734_;
v___y_2710_ = v___y_2735_;
v___y_2711_ = v___y_2736_;
v___y_2712_ = v___y_2737_;
v___y_2713_ = v___y_2738_;
v___y_2714_ = v___y_2739_;
v___y_2715_ = v___y_2740_;
v___y_2716_ = v___y_2741_;
v___y_2717_ = v___y_2742_;
v___y_2718_ = v___y_2743_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___y_2745_;
v___y_2721_ = v___x_2750_;
v___y_2722_ = v___y_2746_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___x_2756_;
goto v___jp_2705_;
}
}
v___jp_2757_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_inc_ref_n(v___y_2763_, 2);
v___x_2777_ = l_Array_append___redArg(v___y_2763_, v___y_2776_);
lean_dec_ref(v___y_2776_);
lean_inc_n(v___y_2773_, 2);
lean_inc_n(v___y_2768_, 2);
v___x_2778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2778_, 0, v___y_2768_);
lean_ctor_set(v___x_2778_, 1, v___y_2773_);
lean_ctor_set(v___x_2778_, 2, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2779_, 0, v___y_2768_);
lean_ctor_set(v___x_2779_, 1, v___y_2773_);
lean_ctor_set(v___x_2779_, 2, v___y_2763_);
v___x_2780_ = l_Lean_Syntax_node5(v___y_2768_, v___y_2759_, v___y_2762_, v___y_2775_, v___y_2769_, v___x_2778_, v___x_2779_);
v___y_2553_ = v___y_2758_;
v___y_2554_ = v___y_2764_;
v___y_2555_ = v___y_2771_;
v_stxForSuggestion_2556_ = v___x_2780_;
v___y_2557_ = v___y_2766_;
v___y_2558_ = v___y_2760_;
v___y_2559_ = v___y_2770_;
v___y_2560_ = v___y_2772_;
v___y_2561_ = v___y_2767_;
v___y_2562_ = v___y_2774_;
v___y_2563_ = v___y_2765_;
v___y_2564_ = v___y_2761_;
goto v___jp_2552_;
}
v___jp_2781_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_inc_ref(v___y_2788_);
v___x_2801_ = l_Array_append___redArg(v___y_2788_, v___y_2800_);
lean_dec_ref(v___y_2800_);
lean_inc(v___y_2798_);
lean_inc(v___y_2793_);
v___x_2802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___y_2793_);
lean_ctor_set(v___x_2802_, 1, v___y_2798_);
lean_ctor_set(v___x_2802_, 2, v___x_2801_);
if (lean_obj_tag(v___y_2787_) == 1)
{
lean_object* v_val_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_val_2803_ = lean_ctor_get(v___y_2787_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v___y_2787_, 1);
v___x_2804_ = l_Lean_SourceInfo_fromRef(v_val_2803_, v___x_2422_);
lean_dec(v_val_2803_);
v___x_2805_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Array_mkArray1___redArg(v___x_2806_);
v___y_2758_ = v___y_2782_;
v___y_2759_ = v___y_2783_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2788_;
v___y_2764_ = v___y_2789_;
v___y_2765_ = v___y_2790_;
v___y_2766_ = v___y_2791_;
v___y_2767_ = v___y_2792_;
v___y_2768_ = v___y_2793_;
v___y_2769_ = v___x_2802_;
v___y_2770_ = v___y_2794_;
v___y_2771_ = v___y_2795_;
v___y_2772_ = v___y_2796_;
v___y_2773_ = v___y_2798_;
v___y_2774_ = v___y_2797_;
v___y_2775_ = v___y_2799_;
v___y_2776_ = v___x_2807_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2808_; 
lean_dec(v___y_2787_);
v___x_2808_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2758_ = v___y_2782_;
v___y_2759_ = v___y_2783_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2788_;
v___y_2764_ = v___y_2789_;
v___y_2765_ = v___y_2790_;
v___y_2766_ = v___y_2791_;
v___y_2767_ = v___y_2792_;
v___y_2768_ = v___y_2793_;
v___y_2769_ = v___x_2802_;
v___y_2770_ = v___y_2794_;
v___y_2771_ = v___y_2795_;
v___y_2772_ = v___y_2796_;
v___y_2773_ = v___y_2798_;
v___y_2774_ = v___y_2797_;
v___y_2775_ = v___y_2799_;
v___y_2776_ = v___x_2808_;
goto v___jp_2757_;
}
}
v___jp_2809_:
{
lean_object* v___x_2825_; lean_object* v_a_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2825_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2811_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = lean_array_get_size(v___y_2810_);
v___x_2828_ = lean_nat_dec_eq(v___x_2827_, v___x_2437_);
if (v___x_2828_ == 0)
{
if (lean_obj_tag(v___y_2813_) == 0)
{
lean_object* v_ref_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_ref_2829_ = lean_ctor_get(v___y_2823_, 2);
v___x_2830_ = l_Lean_SourceInfo_fromRef(v_ref_2829_, v___x_2828_);
v___x_2831_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2832_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2831_);
v___x_2833_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_2834_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2837_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2814_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2839_; 
v_val_2838_ = lean_ctor_get(v___y_2814_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v___y_2814_, 1);
v___x_2839_ = l_Array_mkArray1___redArg(v_val_2838_);
v___y_2615_ = v_stxForExecution_2816_;
v___y_2616_ = v___y_2818_;
v___y_2617_ = v___y_2824_;
v___y_2618_ = v___y_2812_;
v___y_2619_ = v___y_2813_;
v___y_2620_ = v___y_2823_;
v___y_2621_ = v___y_2817_;
v___y_2622_ = v___y_2821_;
v___y_2623_ = v___x_2830_;
v___y_2624_ = v___y_2819_;
v___y_2625_ = v___y_2815_;
v___y_2626_ = v___y_2810_;
v___y_2627_ = v___y_2820_;
v___y_2628_ = v___x_2835_;
v___y_2629_ = v___y_2822_;
v___y_2630_ = v___x_2832_;
v___y_2631_ = v___x_2836_;
v___y_2632_ = v_a_2826_;
v___y_2633_ = v___x_2837_;
v___y_2634_ = v___x_2839_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2840_; 
lean_dec(v___y_2814_);
v___x_2840_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2615_ = v_stxForExecution_2816_;
v___y_2616_ = v___y_2818_;
v___y_2617_ = v___y_2824_;
v___y_2618_ = v___y_2812_;
v___y_2619_ = v___y_2813_;
v___y_2620_ = v___y_2823_;
v___y_2621_ = v___y_2817_;
v___y_2622_ = v___y_2821_;
v___y_2623_ = v___x_2830_;
v___y_2624_ = v___y_2819_;
v___y_2625_ = v___y_2815_;
v___y_2626_ = v___y_2810_;
v___y_2627_ = v___y_2820_;
v___y_2628_ = v___x_2835_;
v___y_2629_ = v___y_2822_;
v___y_2630_ = v___x_2832_;
v___y_2631_ = v___x_2836_;
v___y_2632_ = v_a_2826_;
v___y_2633_ = v___x_2837_;
v___y_2634_ = v___x_2840_;
goto v___jp_2614_;
}
}
else
{
lean_object* v_ref_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_ref_2841_ = lean_ctor_get(v___y_2823_, 2);
v___x_2842_ = l_Lean_SourceInfo_fromRef(v_ref_2841_, v___x_2828_);
v___x_2843_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2844_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2843_);
v___x_2845_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_2846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2849_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2814_) == 1)
{
lean_object* v_val_2850_; lean_object* v___x_2851_; 
v_val_2850_ = lean_ctor_get(v___y_2814_, 0);
lean_inc(v_val_2850_);
lean_dec_ref_known(v___y_2814_, 1);
v___x_2851_ = l_Array_mkArray1___redArg(v_val_2850_);
v___y_2677_ = v___x_2849_;
v___y_2678_ = v___x_2842_;
v___y_2679_ = v_stxForExecution_2816_;
v___y_2680_ = v___y_2818_;
v___y_2681_ = v___y_2824_;
v___y_2682_ = v___y_2812_;
v___y_2683_ = v___y_2813_;
v___y_2684_ = v___y_2823_;
v___y_2685_ = v___y_2817_;
v___y_2686_ = v___y_2821_;
v___y_2687_ = v___x_2844_;
v___y_2688_ = v___y_2819_;
v___y_2689_ = v___y_2815_;
v___y_2690_ = v___y_2810_;
v___y_2691_ = v___y_2820_;
v___y_2692_ = v___x_2847_;
v___y_2693_ = v___y_2822_;
v___y_2694_ = v_a_2826_;
v___y_2695_ = v___x_2848_;
v___y_2696_ = v___x_2851_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2852_; 
lean_dec(v___y_2814_);
v___x_2852_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2677_ = v___x_2849_;
v___y_2678_ = v___x_2842_;
v___y_2679_ = v_stxForExecution_2816_;
v___y_2680_ = v___y_2818_;
v___y_2681_ = v___y_2824_;
v___y_2682_ = v___y_2812_;
v___y_2683_ = v___y_2813_;
v___y_2684_ = v___y_2823_;
v___y_2685_ = v___y_2817_;
v___y_2686_ = v___y_2821_;
v___y_2687_ = v___x_2844_;
v___y_2688_ = v___y_2819_;
v___y_2689_ = v___y_2815_;
v___y_2690_ = v___y_2810_;
v___y_2691_ = v___y_2820_;
v___y_2692_ = v___x_2847_;
v___y_2693_ = v___y_2822_;
v___y_2694_ = v_a_2826_;
v___y_2695_ = v___x_2848_;
v___y_2696_ = v___x_2852_;
goto v___jp_2676_;
}
}
}
else
{
lean_dec_ref(v___y_2810_);
if (lean_obj_tag(v___y_2813_) == 0)
{
lean_object* v_ref_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_ref_2853_ = lean_ctor_get(v___y_2823_, 2);
v___x_2854_ = 0;
v___x_2855_ = l_Lean_SourceInfo_fromRef(v_ref_2853_, v___x_2854_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2857_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2856_);
v___x_2858_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_2859_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2862_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2814_) == 1)
{
lean_object* v_val_2863_; lean_object* v___x_2864_; 
v_val_2863_ = lean_ctor_get(v___y_2814_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v___y_2814_, 1);
v___x_2864_ = l_Array_mkArray1___redArg(v_val_2863_);
v___y_2730_ = v_stxForExecution_2816_;
v___y_2731_ = v___y_2818_;
v___y_2732_ = v___y_2824_;
v___y_2733_ = v___y_2812_;
v___y_2734_ = v___x_2862_;
v___y_2735_ = v___y_2813_;
v___y_2736_ = v___y_2823_;
v___y_2737_ = v___y_2817_;
v___y_2738_ = v___y_2821_;
v___y_2739_ = v___x_2857_;
v___y_2740_ = v___x_2861_;
v___y_2741_ = v___y_2819_;
v___y_2742_ = v___x_2855_;
v___y_2743_ = v___y_2815_;
v___y_2744_ = v___y_2820_;
v___y_2745_ = v___y_2822_;
v___y_2746_ = v___x_2860_;
v___y_2747_ = v_a_2826_;
v___y_2748_ = v___x_2864_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2865_; 
lean_dec(v___y_2814_);
v___x_2865_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2730_ = v_stxForExecution_2816_;
v___y_2731_ = v___y_2818_;
v___y_2732_ = v___y_2824_;
v___y_2733_ = v___y_2812_;
v___y_2734_ = v___x_2862_;
v___y_2735_ = v___y_2813_;
v___y_2736_ = v___y_2823_;
v___y_2737_ = v___y_2817_;
v___y_2738_ = v___y_2821_;
v___y_2739_ = v___x_2857_;
v___y_2740_ = v___x_2861_;
v___y_2741_ = v___y_2819_;
v___y_2742_ = v___x_2855_;
v___y_2743_ = v___y_2815_;
v___y_2744_ = v___y_2820_;
v___y_2745_ = v___y_2822_;
v___y_2746_ = v___x_2860_;
v___y_2747_ = v_a_2826_;
v___y_2748_ = v___x_2865_;
goto v___jp_2729_;
}
}
else
{
lean_object* v_ref_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_ref_2866_ = lean_ctor_get(v___y_2823_, 2);
v___x_2867_ = 0;
v___x_2868_ = l_Lean_SourceInfo_fromRef(v_ref_2866_, v___x_2867_);
v___x_2869_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2870_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2869_);
v___x_2871_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_2872_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2875_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2814_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2877_; 
v_val_2876_ = lean_ctor_get(v___y_2814_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v___y_2814_, 1);
v___x_2877_ = l_Array_mkArray1___redArg(v_val_2876_);
v___y_2782_ = v_stxForExecution_2816_;
v___y_2783_ = v___x_2870_;
v___y_2784_ = v___y_2818_;
v___y_2785_ = v___y_2824_;
v___y_2786_ = v___x_2873_;
v___y_2787_ = v___y_2812_;
v___y_2788_ = v___x_2875_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2823_;
v___y_2791_ = v___y_2817_;
v___y_2792_ = v___y_2821_;
v___y_2793_ = v___x_2868_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2820_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2874_;
v___y_2799_ = v_a_2826_;
v___y_2800_ = v___x_2877_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2878_; 
lean_dec(v___y_2814_);
v___x_2878_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2782_ = v_stxForExecution_2816_;
v___y_2783_ = v___x_2870_;
v___y_2784_ = v___y_2818_;
v___y_2785_ = v___y_2824_;
v___y_2786_ = v___x_2873_;
v___y_2787_ = v___y_2812_;
v___y_2788_ = v___x_2875_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2823_;
v___y_2791_ = v___y_2817_;
v___y_2792_ = v___y_2821_;
v___y_2793_ = v___x_2868_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2820_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2874_;
v___y_2799_ = v_a_2826_;
v___y_2800_ = v___x_2878_;
goto v___jp_2781_;
}
}
}
}
v___jp_2879_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_inc_ref_n(v___y_2886_, 2);
v___x_2901_ = l_Array_append___redArg(v___y_2886_, v___y_2900_);
lean_dec_ref(v___y_2900_);
lean_inc_n(v___y_2894_, 3);
lean_inc_n(v___y_2889_, 5);
v___x_2902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___y_2889_);
lean_ctor_set(v___x_2902_, 1, v___y_2894_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
v___x_2903_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___y_2889_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2906_ = l_Lean_Syntax_SepArray_ofElems(v___x_2905_, v___y_2891_);
v___x_2907_ = l_Array_append___redArg(v___y_2886_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2908_, 0, v___y_2889_);
lean_ctor_set(v___x_2908_, 1, v___y_2894_);
lean_ctor_set(v___x_2908_, 2, v___x_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___y_2889_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_Syntax_node3(v___y_2889_, v___y_2894_, v___x_2904_, v___x_2908_, v___x_2910_);
lean_inc(v___y_2893_);
v___x_2912_ = l_Lean_Syntax_node5(v___y_2889_, v___y_2892_, v___y_2898_, v___y_2893_, v___y_2887_, v___x_2902_, v___x_2911_);
v___y_2810_ = v___y_2891_;
v___y_2811_ = v___y_2893_;
v___y_2812_ = v___y_2881_;
v___y_2813_ = v___y_2882_;
v___y_2814_ = v___y_2897_;
v___y_2815_ = v___y_2890_;
v_stxForExecution_2816_ = v___x_2912_;
v___y_2817_ = v___y_2884_;
v___y_2818_ = v___y_2896_;
v___y_2819_ = v___y_2885_;
v___y_2820_ = v___y_2899_;
v___y_2821_ = v___y_2880_;
v___y_2822_ = v___y_2888_;
v___y_2823_ = v___y_2883_;
v___y_2824_ = v___y_2895_;
goto v___jp_2809_;
}
v___jp_2913_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_inc_ref(v___y_2920_);
v___x_2934_ = l_Array_append___redArg(v___y_2920_, v___y_2933_);
lean_dec_ref(v___y_2933_);
lean_inc(v___y_2927_);
lean_inc(v___y_2921_);
v___x_2935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2935_, 0, v___y_2921_);
lean_ctor_set(v___x_2935_, 1, v___y_2927_);
lean_ctor_set(v___x_2935_, 2, v___x_2934_);
if (lean_obj_tag(v___y_2915_) == 1)
{
lean_object* v_val_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_val_2936_ = lean_ctor_get(v___y_2915_, 0);
v___x_2937_ = l_Lean_SourceInfo_fromRef(v_val_2936_, v___x_2422_);
v___x_2938_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = l_Array_mkArray1___redArg(v___x_2939_);
v___y_2880_ = v___y_2914_;
v___y_2881_ = v___y_2915_;
v___y_2882_ = v___y_2916_;
v___y_2883_ = v___y_2917_;
v___y_2884_ = v___y_2918_;
v___y_2885_ = v___y_2919_;
v___y_2886_ = v___y_2920_;
v___y_2887_ = v___x_2935_;
v___y_2888_ = v___y_2922_;
v___y_2889_ = v___y_2921_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2926_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2929_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2931_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2932_;
v___y_2900_ = v___x_2940_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2941_; 
v___x_2941_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2880_ = v___y_2914_;
v___y_2881_ = v___y_2915_;
v___y_2882_ = v___y_2916_;
v___y_2883_ = v___y_2917_;
v___y_2884_ = v___y_2918_;
v___y_2885_ = v___y_2919_;
v___y_2886_ = v___y_2920_;
v___y_2887_ = v___x_2935_;
v___y_2888_ = v___y_2922_;
v___y_2889_ = v___y_2921_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2926_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2929_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2931_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2932_;
v___y_2900_ = v___x_2941_;
goto v___jp_2879_;
}
}
v___jp_2942_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_inc_ref_n(v___y_2955_, 2);
v___x_2964_ = l_Array_append___redArg(v___y_2955_, v___y_2963_);
lean_dec_ref(v___y_2963_);
lean_inc_n(v___y_2948_, 3);
lean_inc_n(v___y_2943_, 5);
v___x_2965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2965_, 0, v___y_2943_);
lean_ctor_set(v___x_2965_, 1, v___y_2948_);
lean_ctor_set(v___x_2965_, 2, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___y_2943_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2969_ = l_Lean_Syntax_SepArray_ofElems(v___x_2968_, v___y_2956_);
v___x_2970_ = l_Array_append___redArg(v___y_2955_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2943_);
lean_ctor_set(v___x_2971_, 1, v___y_2948_);
lean_ctor_set(v___x_2971_, 2, v___x_2970_);
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___y_2943_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_Syntax_node3(v___y_2943_, v___y_2948_, v___x_2967_, v___x_2971_, v___x_2973_);
lean_inc(v___y_2957_);
v___x_2975_ = l_Lean_Syntax_node5(v___y_2943_, v___y_2961_, v___y_2953_, v___y_2957_, v___y_2951_, v___x_2965_, v___x_2974_);
v___y_2810_ = v___y_2956_;
v___y_2811_ = v___y_2957_;
v___y_2812_ = v___y_2945_;
v___y_2813_ = v___y_2946_;
v___y_2814_ = v___y_2960_;
v___y_2815_ = v___y_2954_;
v_stxForExecution_2816_ = v___x_2975_;
v___y_2817_ = v___y_2949_;
v___y_2818_ = v___y_2959_;
v___y_2819_ = v___y_2950_;
v___y_2820_ = v___y_2962_;
v___y_2821_ = v___y_2944_;
v___y_2822_ = v___y_2952_;
v___y_2823_ = v___y_2947_;
v___y_2824_ = v___y_2958_;
goto v___jp_2809_;
}
v___jp_2976_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_inc_ref(v___y_2989_);
v___x_2997_ = l_Array_append___redArg(v___y_2989_, v___y_2996_);
lean_dec_ref(v___y_2996_);
lean_inc(v___y_2982_);
lean_inc(v___y_2977_);
v___x_2998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2998_, 0, v___y_2977_);
lean_ctor_set(v___x_2998_, 1, v___y_2982_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
if (lean_obj_tag(v___y_2979_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_val_2999_ = lean_ctor_get(v___y_2979_, 0);
v___x_3000_ = l_Lean_SourceInfo_fromRef(v_val_2999_, v___x_2422_);
v___x_3001_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Array_mkArray1___redArg(v___x_3002_);
v___y_2943_ = v___y_2977_;
v___y_2944_ = v___y_2978_;
v___y_2945_ = v___y_2979_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___y_2982_;
v___y_2949_ = v___y_2983_;
v___y_2950_ = v___y_2984_;
v___y_2951_ = v___x_2998_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2986_;
v___y_2954_ = v___y_2987_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2988_;
v___y_2957_ = v___y_2990_;
v___y_2958_ = v___y_2992_;
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v___y_2995_;
v___y_2962_ = v___y_2994_;
v___y_2963_ = v___x_3003_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_3004_; 
v___x_3004_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2943_ = v___y_2977_;
v___y_2944_ = v___y_2978_;
v___y_2945_ = v___y_2979_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___y_2982_;
v___y_2949_ = v___y_2983_;
v___y_2950_ = v___y_2984_;
v___y_2951_ = v___x_2998_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2986_;
v___y_2954_ = v___y_2987_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2988_;
v___y_2957_ = v___y_2990_;
v___y_2958_ = v___y_2992_;
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v___y_2995_;
v___y_2962_ = v___y_2994_;
v___y_2963_ = v___x_3004_;
goto v___jp_2942_;
}
}
v___jp_3005_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_inc_ref_n(v___y_3021_, 2);
v___x_3027_ = l_Array_append___redArg(v___y_3021_, v___y_3026_);
lean_dec_ref(v___y_3026_);
lean_inc_n(v___y_3006_, 2);
lean_inc_n(v___y_3019_, 2);
v___x_3028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3028_, 0, v___y_3019_);
lean_ctor_set(v___x_3028_, 1, v___y_3006_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3029_, 0, v___y_3019_);
lean_ctor_set(v___x_3029_, 1, v___y_3006_);
lean_ctor_set(v___x_3029_, 2, v___y_3021_);
lean_inc(v___y_3017_);
v___x_3030_ = l_Lean_Syntax_node5(v___y_3019_, v___y_3016_, v___y_3022_, v___y_3017_, v___y_3023_, v___x_3028_, v___x_3029_);
v___y_2810_ = v___y_3015_;
v___y_2811_ = v___y_3017_;
v___y_2812_ = v___y_3008_;
v___y_2813_ = v___y_3009_;
v___y_2814_ = v___y_3024_;
v___y_2815_ = v___y_3014_;
v_stxForExecution_2816_ = v___x_3030_;
v___y_2817_ = v___y_3011_;
v___y_2818_ = v___y_3020_;
v___y_2819_ = v___y_3012_;
v___y_2820_ = v___y_3025_;
v___y_2821_ = v___y_3007_;
v___y_2822_ = v___y_3013_;
v___y_2823_ = v___y_3010_;
v___y_2824_ = v___y_3018_;
goto v___jp_2809_;
}
v___jp_3031_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_inc_ref(v___y_3048_);
v___x_3052_ = l_Array_append___redArg(v___y_3048_, v___y_3051_);
lean_dec_ref(v___y_3051_);
lean_inc(v___y_3032_);
lean_inc(v___y_3046_);
v___x_3053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3046_);
lean_ctor_set(v___x_3053_, 1, v___y_3032_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
if (lean_obj_tag(v___y_3034_) == 1)
{
lean_object* v_val_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_val_3054_ = lean_ctor_get(v___y_3034_, 0);
v___x_3055_ = l_Lean_SourceInfo_fromRef(v_val_3054_, v___x_2422_);
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Array_mkArray1___redArg(v___x_3057_);
v___y_3006_ = v___y_3032_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3034_;
v___y_3009_ = v___y_3035_;
v___y_3010_ = v___y_3036_;
v___y_3011_ = v___y_3037_;
v___y_3012_ = v___y_3038_;
v___y_3013_ = v___y_3039_;
v___y_3014_ = v___y_3040_;
v___y_3015_ = v___y_3041_;
v___y_3016_ = v___y_3042_;
v___y_3017_ = v___y_3043_;
v___y_3018_ = v___y_3045_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3044_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3047_;
v___y_3023_ = v___x_3053_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3050_;
v___y_3026_ = v___x_3058_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3006_ = v___y_3032_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3034_;
v___y_3009_ = v___y_3035_;
v___y_3010_ = v___y_3036_;
v___y_3011_ = v___y_3037_;
v___y_3012_ = v___y_3038_;
v___y_3013_ = v___y_3039_;
v___y_3014_ = v___y_3040_;
v___y_3015_ = v___y_3041_;
v___y_3016_ = v___y_3042_;
v___y_3017_ = v___y_3043_;
v___y_3018_ = v___y_3045_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3044_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3047_;
v___y_3023_ = v___x_3053_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3050_;
v___y_3026_ = v___x_3059_;
goto v___jp_3005_;
}
}
v___jp_3060_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_inc_ref_n(v___y_3078_, 2);
v___x_3082_ = l_Array_append___redArg(v___y_3078_, v___y_3081_);
lean_dec_ref(v___y_3081_);
lean_inc_n(v___y_3077_, 2);
lean_inc_n(v___y_3075_, 2);
v___x_3083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3075_);
lean_ctor_set(v___x_3083_, 1, v___y_3077_);
lean_ctor_set(v___x_3083_, 2, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3075_);
lean_ctor_set(v___x_3084_, 1, v___y_3077_);
lean_ctor_set(v___x_3084_, 2, v___y_3078_);
lean_inc(v___y_3071_);
v___x_3085_ = l_Lean_Syntax_node5(v___y_3075_, v___y_3074_, v___y_3079_, v___y_3071_, v___y_3067_, v___x_3083_, v___x_3084_);
v___y_2810_ = v___y_3070_;
v___y_2811_ = v___y_3071_;
v___y_2812_ = v___y_3062_;
v___y_2813_ = v___y_3063_;
v___y_2814_ = v___y_3076_;
v___y_2815_ = v___y_3069_;
v_stxForExecution_2816_ = v___x_3085_;
v___y_2817_ = v___y_3065_;
v___y_2818_ = v___y_3073_;
v___y_2819_ = v___y_3066_;
v___y_2820_ = v___y_3080_;
v___y_2821_ = v___y_3061_;
v___y_2822_ = v___y_3068_;
v___y_2823_ = v___y_3064_;
v___y_2824_ = v___y_3072_;
goto v___jp_2809_;
}
v___jp_3086_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_inc_ref(v___y_3103_);
v___x_3107_ = l_Array_append___redArg(v___y_3103_, v___y_3106_);
lean_dec_ref(v___y_3106_);
lean_inc(v___y_3102_);
lean_inc(v___y_3100_);
v___x_3108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___y_3100_);
lean_ctor_set(v___x_3108_, 1, v___y_3102_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
if (lean_obj_tag(v___y_3088_) == 1)
{
lean_object* v_val_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_val_3109_ = lean_ctor_get(v___y_3088_, 0);
v___x_3110_ = l_Lean_SourceInfo_fromRef(v_val_3109_, v___x_2422_);
v___x_3111_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = l_Array_mkArray1___redArg(v___x_3112_);
v___y_3061_ = v___y_3087_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___y_3090_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3092_;
v___y_3067_ = v___x_3108_;
v___y_3068_ = v___y_3093_;
v___y_3069_ = v___y_3094_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3098_;
v___y_3073_ = v___y_3097_;
v___y_3074_ = v___y_3099_;
v___y_3075_ = v___y_3100_;
v___y_3076_ = v___y_3101_;
v___y_3077_ = v___y_3102_;
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___y_3105_;
v___y_3080_ = v___y_3104_;
v___y_3081_ = v___x_3113_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3061_ = v___y_3087_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___y_3090_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3092_;
v___y_3067_ = v___x_3108_;
v___y_3068_ = v___y_3093_;
v___y_3069_ = v___y_3094_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3098_;
v___y_3073_ = v___y_3097_;
v___y_3074_ = v___y_3099_;
v___y_3075_ = v___y_3100_;
v___y_3076_ = v___y_3101_;
v___y_3077_ = v___y_3102_;
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___y_3105_;
v___y_3080_ = v___y_3104_;
v___y_3081_ = v___x_3114_;
goto v___jp_3060_;
}
}
v___jp_3115_:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = lean_array_get_size(v_argsArray_3121_);
v___x_3131_ = lean_nat_dec_eq(v___x_3130_, v___x_2437_);
if (v___x_3131_ == 0)
{
if (lean_obj_tag(v___y_3118_) == 0)
{
lean_object* v_ref_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_ref_3132_ = lean_ctor_get(v___y_3128_, 2);
v___x_3133_ = l_Lean_SourceInfo_fromRef(v_ref_3132_, v___x_3131_);
v___x_3134_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3135_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3134_);
v___x_3136_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_3137_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3140_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3119_) == 1)
{
lean_object* v_val_3141_; lean_object* v___x_3142_; 
v_val_3141_ = lean_ctor_get(v___y_3119_, 0);
lean_inc(v_val_3141_);
v___x_3142_ = l_Array_mkArray1___redArg(v_val_3141_);
v___y_2914_ = v___y_3126_;
v___y_2915_ = v___y_3117_;
v___y_2916_ = v___y_3118_;
v___y_2917_ = v___y_3128_;
v___y_2918_ = v___y_3122_;
v___y_2919_ = v___y_3124_;
v___y_2920_ = v___x_3140_;
v___y_2921_ = v___x_3133_;
v___y_2922_ = v___y_3127_;
v___y_2923_ = v___y_3120_;
v___y_2924_ = v_argsArray_3121_;
v___y_2925_ = v___y_3116_;
v___y_2926_ = v___x_3135_;
v___y_2927_ = v___x_3139_;
v___y_2928_ = v___y_3123_;
v___y_2929_ = v___y_3129_;
v___y_2930_ = v___x_3138_;
v___y_2931_ = v___y_3119_;
v___y_2932_ = v___y_3125_;
v___y_2933_ = v___x_3142_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_3143_; 
v___x_3143_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2914_ = v___y_3126_;
v___y_2915_ = v___y_3117_;
v___y_2916_ = v___y_3118_;
v___y_2917_ = v___y_3128_;
v___y_2918_ = v___y_3122_;
v___y_2919_ = v___y_3124_;
v___y_2920_ = v___x_3140_;
v___y_2921_ = v___x_3133_;
v___y_2922_ = v___y_3127_;
v___y_2923_ = v___y_3120_;
v___y_2924_ = v_argsArray_3121_;
v___y_2925_ = v___y_3116_;
v___y_2926_ = v___x_3135_;
v___y_2927_ = v___x_3139_;
v___y_2928_ = v___y_3123_;
v___y_2929_ = v___y_3129_;
v___y_2930_ = v___x_3138_;
v___y_2931_ = v___y_3119_;
v___y_2932_ = v___y_3125_;
v___y_2933_ = v___x_3143_;
goto v___jp_2913_;
}
}
else
{
lean_object* v_ref_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_ref_3144_ = lean_ctor_get(v___y_3128_, 2);
v___x_3145_ = l_Lean_SourceInfo_fromRef(v_ref_3144_, v___x_3131_);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3147_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3146_);
v___x_3148_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_3149_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3152_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3119_) == 1)
{
lean_object* v_val_3153_; lean_object* v___x_3154_; 
v_val_3153_ = lean_ctor_get(v___y_3119_, 0);
lean_inc(v_val_3153_);
v___x_3154_ = l_Array_mkArray1___redArg(v_val_3153_);
v___y_2977_ = v___x_3145_;
v___y_2978_ = v___y_3126_;
v___y_2979_ = v___y_3117_;
v___y_2980_ = v___y_3118_;
v___y_2981_ = v___y_3128_;
v___y_2982_ = v___x_3151_;
v___y_2983_ = v___y_3122_;
v___y_2984_ = v___y_3124_;
v___y_2985_ = v___y_3127_;
v___y_2986_ = v___x_3150_;
v___y_2987_ = v___y_3120_;
v___y_2988_ = v_argsArray_3121_;
v___y_2989_ = v___x_3152_;
v___y_2990_ = v___y_3116_;
v___y_2991_ = v___y_3123_;
v___y_2992_ = v___y_3129_;
v___y_2993_ = v___y_3119_;
v___y_2994_ = v___y_3125_;
v___y_2995_ = v___x_3147_;
v___y_2996_ = v___x_3154_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2977_ = v___x_3145_;
v___y_2978_ = v___y_3126_;
v___y_2979_ = v___y_3117_;
v___y_2980_ = v___y_3118_;
v___y_2981_ = v___y_3128_;
v___y_2982_ = v___x_3151_;
v___y_2983_ = v___y_3122_;
v___y_2984_ = v___y_3124_;
v___y_2985_ = v___y_3127_;
v___y_2986_ = v___x_3150_;
v___y_2987_ = v___y_3120_;
v___y_2988_ = v_argsArray_3121_;
v___y_2989_ = v___x_3152_;
v___y_2990_ = v___y_3116_;
v___y_2991_ = v___y_3123_;
v___y_2992_ = v___y_3129_;
v___y_2993_ = v___y_3119_;
v___y_2994_ = v___y_3125_;
v___y_2995_ = v___x_3147_;
v___y_2996_ = v___x_3155_;
goto v___jp_2976_;
}
}
}
else
{
if (lean_obj_tag(v___y_3118_) == 0)
{
lean_object* v_ref_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_ref_3156_ = lean_ctor_get(v___y_3128_, 2);
v___x_3157_ = 0;
v___x_3158_ = l_Lean_SourceInfo_fromRef(v_ref_3156_, v___x_3157_);
v___x_3159_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3160_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3159_);
v___x_3161_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_3162_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3165_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3119_) == 1)
{
lean_object* v_val_3166_; lean_object* v___x_3167_; 
v_val_3166_ = lean_ctor_get(v___y_3119_, 0);
lean_inc(v_val_3166_);
v___x_3167_ = l_Array_mkArray1___redArg(v_val_3166_);
v___y_3032_ = v___x_3164_;
v___y_3033_ = v___y_3126_;
v___y_3034_ = v___y_3117_;
v___y_3035_ = v___y_3118_;
v___y_3036_ = v___y_3128_;
v___y_3037_ = v___y_3122_;
v___y_3038_ = v___y_3124_;
v___y_3039_ = v___y_3127_;
v___y_3040_ = v___y_3120_;
v___y_3041_ = v_argsArray_3121_;
v___y_3042_ = v___x_3160_;
v___y_3043_ = v___y_3116_;
v___y_3044_ = v___y_3123_;
v___y_3045_ = v___y_3129_;
v___y_3046_ = v___x_3158_;
v___y_3047_ = v___x_3163_;
v___y_3048_ = v___x_3165_;
v___y_3049_ = v___y_3119_;
v___y_3050_ = v___y_3125_;
v___y_3051_ = v___x_3167_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3168_; 
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3032_ = v___x_3164_;
v___y_3033_ = v___y_3126_;
v___y_3034_ = v___y_3117_;
v___y_3035_ = v___y_3118_;
v___y_3036_ = v___y_3128_;
v___y_3037_ = v___y_3122_;
v___y_3038_ = v___y_3124_;
v___y_3039_ = v___y_3127_;
v___y_3040_ = v___y_3120_;
v___y_3041_ = v_argsArray_3121_;
v___y_3042_ = v___x_3160_;
v___y_3043_ = v___y_3116_;
v___y_3044_ = v___y_3123_;
v___y_3045_ = v___y_3129_;
v___y_3046_ = v___x_3158_;
v___y_3047_ = v___x_3163_;
v___y_3048_ = v___x_3165_;
v___y_3049_ = v___y_3119_;
v___y_3050_ = v___y_3125_;
v___y_3051_ = v___x_3168_;
goto v___jp_3031_;
}
}
else
{
lean_object* v_ref_3169_; uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_ref_3169_ = lean_ctor_get(v___y_3128_, 2);
v___x_3170_ = 0;
v___x_3171_ = l_Lean_SourceInfo_fromRef(v_ref_3169_, v___x_3170_);
v___x_3172_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3173_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3172_);
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_tk_2438_, v___x_2422_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3178_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3119_) == 1)
{
lean_object* v_val_3179_; lean_object* v___x_3180_; 
v_val_3179_ = lean_ctor_get(v___y_3119_, 0);
lean_inc(v_val_3179_);
v___x_3180_ = l_Array_mkArray1___redArg(v_val_3179_);
v___y_3087_ = v___y_3126_;
v___y_3088_ = v___y_3117_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3128_;
v___y_3091_ = v___y_3122_;
v___y_3092_ = v___y_3124_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v_argsArray_3121_;
v___y_3096_ = v___y_3116_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3129_;
v___y_3099_ = v___x_3173_;
v___y_3100_ = v___x_3171_;
v___y_3101_ = v___y_3119_;
v___y_3102_ = v___x_3177_;
v___y_3103_ = v___x_3178_;
v___y_3104_ = v___y_3125_;
v___y_3105_ = v___x_3176_;
v___y_3106_ = v___x_3180_;
goto v___jp_3086_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3087_ = v___y_3126_;
v___y_3088_ = v___y_3117_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3128_;
v___y_3091_ = v___y_3122_;
v___y_3092_ = v___y_3124_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v_argsArray_3121_;
v___y_3096_ = v___y_3116_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3129_;
v___y_3099_ = v___x_3173_;
v___y_3100_ = v___x_3171_;
v___y_3101_ = v___y_3119_;
v___y_3102_ = v___x_3177_;
v___y_3103_ = v___x_3178_;
v___y_3104_ = v___y_3125_;
v___y_3105_ = v___x_3176_;
v___y_3106_ = v___x_3181_;
goto v___jp_3086_;
}
}
}
}
v___jp_3182_:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3189_, v___y_3187_, v___y_3184_, v___y_3185_, v___y_3194_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3200_ = l_Lean_LibrarySuggestions_select(v_a_3199_, v___y_3197_, v___y_3187_, v___y_3184_, v___y_3185_, v___y_3194_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; size_t v_sz_3202_; size_t v___x_3203_; lean_object* v___x_3204_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v_sz_3202_ = lean_array_size(v_a_3201_);
v___x_3203_ = ((size_t)0ULL);
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3201_, v_sz_3202_, v___x_3203_, v___y_3196_, v___y_3190_, v___y_3189_, v___y_3192_, v___y_3188_, v___y_3187_, v___y_3184_, v___y_3185_, v___y_3194_);
lean_dec(v_a_3201_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___y_3116_ = v___y_3193_;
v___y_3117_ = v___y_3183_;
v___y_3118_ = v___y_3186_;
v___y_3119_ = v___y_3195_;
v___y_3120_ = v___y_3191_;
v_argsArray_3121_ = v_a_3205_;
v___y_3122_ = v___y_3190_;
v___y_3123_ = v___y_3189_;
v___y_3124_ = v___y_3192_;
v___y_3125_ = v___y_3188_;
v___y_3126_ = v___y_3187_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v___y_3185_;
v___y_3129_ = v___y_3194_;
goto v___jp_3115_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v___y_3195_);
lean_dec(v___y_3193_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v_a_3206_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3204_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3204_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec(v___y_3193_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v_a_3214_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3200_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3200_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec(v___y_3193_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v_a_3222_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3198_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3198_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
v___jp_3230_:
{
lean_object* v_config_3246_; uint8_t v_suggestions_3247_; 
v_config_3246_ = lean_ctor_get(v___y_3237_, 0);
lean_inc_ref(v_config_3246_);
lean_dec_ref(v___y_3237_);
v_suggestions_3247_ = lean_ctor_get_uint8(v_config_3246_, sizeof(void*)*3 + 26);
if (v_suggestions_3247_ == 0)
{
lean_dec_ref(v_config_3246_);
lean_dec_ref(v___f_2426_);
v___y_3116_ = v___y_3242_;
v___y_3117_ = v___y_3231_;
v___y_3118_ = v___y_3234_;
v___y_3119_ = v___y_3244_;
v___y_3120_ = v___y_3240_;
v_argsArray_3121_ = v___y_3245_;
v___y_3122_ = v___y_3239_;
v___y_3123_ = v___y_3238_;
v___y_3124_ = v___y_3241_;
v___y_3125_ = v___y_3236_;
v___y_3126_ = v___y_3235_;
v___y_3127_ = v___y_3232_;
v___y_3128_ = v___y_3233_;
v___y_3129_ = v___y_3243_;
goto v___jp_3115_;
}
else
{
lean_object* v_maxSuggestions_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_maxSuggestions_3248_ = lean_ctor_get(v_config_3246_, 2);
lean_inc(v_maxSuggestions_3248_);
lean_dec_ref(v_config_3246_);
v___x_3249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3250_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3248_) == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_unsigned_to_nat(100u);
v___x_3252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3249_);
lean_ctor_set(v___x_3252_, 2, v___f_2426_);
lean_ctor_set(v___x_3252_, 3, v___x_3250_);
v___y_3183_ = v___y_3231_;
v___y_3184_ = v___y_3232_;
v___y_3185_ = v___y_3233_;
v___y_3186_ = v___y_3234_;
v___y_3187_ = v___y_3235_;
v___y_3188_ = v___y_3236_;
v___y_3189_ = v___y_3238_;
v___y_3190_ = v___y_3239_;
v___y_3191_ = v___y_3240_;
v___y_3192_ = v___y_3241_;
v___y_3193_ = v___y_3242_;
v___y_3194_ = v___y_3243_;
v___y_3195_ = v___y_3244_;
v___y_3196_ = v___y_3245_;
v___y_3197_ = v___x_3252_;
goto v___jp_3182_;
}
else
{
lean_object* v_val_3253_; lean_object* v___x_3254_; 
v_val_3253_ = lean_ctor_get(v_maxSuggestions_3248_, 0);
lean_inc(v_val_3253_);
lean_dec_ref_known(v_maxSuggestions_3248_, 1);
v___x_3254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3254_, 0, v_val_3253_);
lean_ctor_set(v___x_3254_, 1, v___x_3249_);
lean_ctor_set(v___x_3254_, 2, v___f_2426_);
lean_ctor_set(v___x_3254_, 3, v___x_3250_);
v___y_3183_ = v___y_3231_;
v___y_3184_ = v___y_3232_;
v___y_3185_ = v___y_3233_;
v___y_3186_ = v___y_3234_;
v___y_3187_ = v___y_3235_;
v___y_3188_ = v___y_3236_;
v___y_3189_ = v___y_3238_;
v___y_3190_ = v___y_3239_;
v___y_3191_ = v___y_3240_;
v___y_3192_ = v___y_3241_;
v___y_3193_ = v___y_3242_;
v___y_3194_ = v___y_3243_;
v___y_3195_ = v___y_3244_;
v___y_3196_ = v___y_3245_;
v___y_3197_ = v___x_3254_;
goto v___jp_3182_;
}
}
}
v___jp_3255_:
{
uint8_t v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = 1;
lean_inc(v___y_3266_);
v___x_3270_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3266_, v___x_3269_, v___y_3263_, v___y_3259_, v___y_3267_);
if (lean_obj_tag(v___x_3270_) == 0)
{
if (lean_obj_tag(v___y_3265_) == 1)
{
lean_object* v_a_3271_; lean_object* v_val_3272_; lean_object* v___x_3273_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v_val_3272_ = lean_ctor_get(v___y_3265_, 0);
lean_inc(v_val_3272_);
lean_dec_ref_known(v___y_3265_, 1);
v___x_3273_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3272_);
lean_dec(v_val_3272_);
v___y_3231_ = v___y_3256_;
v___y_3232_ = v___y_3257_;
v___y_3233_ = v___y_3259_;
v___y_3234_ = v___y_3258_;
v___y_3235_ = v___y_3260_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v_a_3271_;
v___y_3238_ = v___y_3262_;
v___y_3239_ = v___y_3263_;
v___y_3240_ = v___x_3269_;
v___y_3241_ = v___y_3264_;
v___y_3242_ = v___y_3266_;
v___y_3243_ = v___y_3267_;
v___y_3244_ = v___y_3268_;
v___y_3245_ = v___x_3273_;
goto v___jp_3230_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3275_; 
lean_dec(v___y_3265_);
v_a_3274_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3275_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3231_ = v___y_3256_;
v___y_3232_ = v___y_3257_;
v___y_3233_ = v___y_3259_;
v___y_3234_ = v___y_3258_;
v___y_3235_ = v___y_3260_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v_a_3274_;
v___y_3238_ = v___y_3262_;
v___y_3239_ = v___y_3263_;
v___y_3240_ = v___x_3269_;
v___y_3241_ = v___y_3264_;
v___y_3242_ = v___y_3266_;
v___y_3243_ = v___y_3267_;
v___y_3244_ = v___y_3268_;
v___y_3245_ = v___x_3275_;
goto v___jp_3230_;
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v___y_3268_);
lean_dec(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec(v___y_3258_);
lean_dec(v___y_3256_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v_a_3276_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3270_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3270_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
v___jp_3284_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Syntax_getOptional_x3f(v___y_3288_);
lean_dec(v___y_3288_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3295_;
v___y_3258_ = v___y_3287_;
v___y_3259_ = v___y_3296_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3293_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___y_3290_;
v___y_3264_ = v___y_3292_;
v___y_3265_ = v_args_3289_;
v___y_3266_ = v___y_3285_;
v___y_3267_ = v___y_3297_;
v___y_3268_ = v___x_3299_;
goto v___jp_3255_;
}
else
{
lean_object* v_val_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_val_3300_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3298_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_val_3300_);
lean_dec(v___x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3295_;
v___y_3258_ = v___y_3287_;
v___y_3259_ = v___y_3296_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3293_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___y_3290_;
v___y_3264_ = v___y_3292_;
v___y_3265_ = v_args_3289_;
v___y_3266_ = v___y_3285_;
v___y_3267_ = v___y_3297_;
v___y_3268_ = v___x_3305_;
goto v___jp_3255_;
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_unsigned_to_nat(3u);
v___x_3324_ = l_Lean_Syntax_getArg(v___y_3311_, v___x_3323_);
lean_dec(v___y_3311_);
v___x_3325_ = l_Lean_Syntax_isNone(v___x_3324_);
if (v___x_3325_ == 0)
{
uint8_t v___x_3326_; 
lean_inc(v___x_3324_);
v___x_3326_ = l_Lean_Syntax_matchesNull(v___x_3324_, v___x_3308_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_dec(v___x_3324_);
lean_dec(v_o_3314_);
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3328_ = l_Lean_Syntax_getArg(v___x_3324_, v___x_2437_);
lean_dec(v___x_3324_);
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3330_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3329_);
lean_inc(v___x_3328_);
v___x_3331_ = l_Lean_Syntax_isOfKind(v___x_3328_, v___x_3330_);
lean_dec(v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
lean_dec(v___x_3328_);
lean_dec(v_o_3314_);
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3332_;
}
else
{
lean_object* v___x_3333_; lean_object* v_args_3334_; lean_object* v___x_3335_; 
v___x_3333_ = l_Lean_Syntax_getArg(v___x_3328_, v___x_3308_);
lean_dec(v___x_3328_);
v_args_3334_ = l_Lean_Syntax_getArgs(v___x_3333_);
lean_dec(v___x_3333_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_args_3334_);
v___y_3285_ = v___y_3310_;
v___y_3286_ = v_o_3314_;
v___y_3287_ = v___y_3312_;
v___y_3288_ = v___y_3313_;
v_args_3289_ = v___x_3335_;
v___y_3290_ = v___y_3315_;
v___y_3291_ = v___y_3316_;
v___y_3292_ = v___y_3317_;
v___y_3293_ = v___y_3318_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3320_;
v___y_3296_ = v___y_3321_;
v___y_3297_ = v___y_3322_;
goto v___jp_3284_;
}
}
}
else
{
lean_object* v___x_3336_; 
lean_dec(v___x_3324_);
v___x_3336_ = lean_box(0);
v___y_3285_ = v___y_3310_;
v___y_3286_ = v_o_3314_;
v___y_3287_ = v___y_3312_;
v___y_3288_ = v___y_3313_;
v_args_3289_ = v___x_3336_;
v___y_3290_ = v___y_3315_;
v___y_3291_ = v___y_3316_;
v___y_3292_ = v___y_3317_;
v___y_3293_ = v___y_3318_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3320_;
v___y_3296_ = v___y_3321_;
v___y_3297_ = v___y_3322_;
goto v___jp_3284_;
}
}
v___jp_3337_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3347_ = lean_unsigned_to_nat(2u);
v___x_3348_ = l_Lean_Syntax_getArg(v_stx_2421_, v___x_3347_);
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3350_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3349_);
lean_inc(v___x_3348_);
v___x_3351_ = l_Lean_Syntax_isOfKind(v___x_3348_, v___x_3350_);
lean_dec(v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec(v___x_3348_);
lean_dec(v_bang_3338_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3352_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3352_;
}
else
{
lean_object* v_cfg_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_cfg_3353_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_2437_);
v___x_3354_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2425_);
lean_inc_ref(v___x_2424_);
lean_inc_ref(v___x_2423_);
v___x_3355_ = l_Lean_Name_mkStr4(v___x_2423_, v___x_2424_, v___x_2425_, v___x_3354_);
lean_inc(v_cfg_3353_);
v___x_3356_ = l_Lean_Syntax_isOfKind(v_cfg_3353_, v___x_3355_);
lean_dec(v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
lean_dec(v_cfg_3353_);
lean_dec(v___x_3348_);
lean_dec(v_bang_3338_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3358_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3308_);
v___x_3359_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3347_);
v___x_3360_ = l_Lean_Syntax_isNone(v___x_3359_);
if (v___x_3360_ == 0)
{
uint8_t v___x_3361_; 
lean_inc(v___x_3359_);
v___x_3361_ = l_Lean_Syntax_matchesNull(v___x_3359_, v___x_3308_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec(v___x_3359_);
lean_dec(v___x_3358_);
lean_dec(v_cfg_3353_);
lean_dec(v___x_3348_);
lean_dec(v_bang_3338_);
lean_dec(v_tk_2438_);
lean_dec_ref(v___f_2426_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
v___x_3362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3362_;
}
else
{
lean_object* v_o_3363_; lean_object* v___x_3364_; 
v_o_3363_ = l_Lean_Syntax_getArg(v___x_3359_, v___x_2437_);
lean_dec(v___x_3359_);
v___x_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_o_3363_);
v___y_3310_ = v_cfg_3353_;
v___y_3311_ = v___x_3348_;
v___y_3312_ = v_bang_3338_;
v___y_3313_ = v___x_3358_;
v_o_3314_ = v___x_3364_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3340_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___y_3342_;
v___y_3319_ = v___y_3343_;
v___y_3320_ = v___y_3344_;
v___y_3321_ = v___y_3345_;
v___y_3322_ = v___y_3346_;
goto v___jp_3309_;
}
}
else
{
lean_object* v___x_3365_; 
lean_dec(v___x_3359_);
v___x_3365_ = lean_box(0);
v___y_3310_ = v_cfg_3353_;
v___y_3311_ = v___x_3348_;
v___y_3312_ = v_bang_3338_;
v___y_3313_ = v___x_3358_;
v_o_3314_ = v___x_3365_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3340_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___y_3342_;
v___y_3319_ = v___y_3343_;
v___y_3320_ = v___y_3344_;
v___y_3321_ = v___y_3345_;
v___y_3322_ = v___y_3346_;
goto v___jp_3309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3373_, lean_object* v_stx_3374_, lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v___x_3378_, lean_object* v___f_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v___x_30635__boxed_3389_; uint8_t v___x_30636__boxed_3390_; lean_object* v_res_3391_; 
v___x_30635__boxed_3389_ = lean_unbox(v___x_3373_);
v___x_30636__boxed_3390_ = lean_unbox(v___x_3375_);
v_res_3391_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_30635__boxed_3389_, v_stx_3374_, v___x_30636__boxed_3390_, v___x_3376_, v___x_3377_, v___x_3378_, v___f_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v_stx_3374_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; uint8_t v___x_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___y_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3398_);
v___x_3412_ = l_Lean_Syntax_isOfKind(v_stx_3398_, v___x_3411_);
v___x_3413_ = 1;
v___f_3414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3415_ = lean_box(v___x_3412_);
v___x_3416_ = lean_box(v___x_3413_);
v___y_3417_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3417_, 0, v___x_3415_);
lean_closure_set(v___y_3417_, 1, v_stx_3398_);
lean_closure_set(v___y_3417_, 2, v___x_3416_);
lean_closure_set(v___y_3417_, 3, v___x_3408_);
lean_closure_set(v___y_3417_, 4, v___x_3409_);
lean_closure_set(v___y_3417_, 5, v___x_3410_);
lean_closure_set(v___y_3417_, 6, v___f_3414_);
v___x_3418_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3418_, 0, v___y_3417_);
v___x_3419_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3418_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3431_, lean_object* v_as_3432_, lean_object* v_as_x27_3433_, lean_object* v_b_3434_, lean_object* v_a_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3431_, v_as_x27_3433_, v_b_3434_, v___y_3442_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3446_, lean_object* v_as_3447_, lean_object* v_as_x27_3448_, lean_object* v_b_3449_, lean_object* v_a_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3446_, v_as_3447_, v_as_x27_3448_, v_b_3449_, v_a_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v_as_x27_3448_);
lean_dec(v_as_3447_);
lean_dec(v___x_3446_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3468_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3469_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3471_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3472_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3468_, v___x_3469_, v___x_3470_, v___x_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3502_ = l_Lean_addBuiltinDeclarationRanges(v___x_3500_, v___x_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3505_, lean_object* v_simprocs_3506_, lean_object* v_fvarIdsToSimp_3507_, uint8_t v_simplifyTarget_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = lean_unsigned_to_nat(32u);
v___x_3518_ = lean_mk_empty_array_with_capacity(v___x_3517_);
lean_dec_ref(v___x_3518_);
v___x_3519_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3520_ = l_Lean_Meta_dsimpGoal(v_a_3516_, v_ctx_3505_, v_simprocs_3506_, v_simplifyTarget_3508_, v_fvarIdsToSimp_3507_, v___x_3519_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_fst_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
if (lean_obj_tag(v_fst_3522_) == 0)
{
lean_object* v_snd_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_snd_3523_ = lean_ctor_get(v_a_3521_, 1);
lean_inc(v_snd_3523_);
lean_dec(v_a_3521_);
v___x_3524_ = lean_box(0);
v___x_3525_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3524_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3525_, 0);
lean_dec(v_unused_3533_);
v___x_3527_ = v___x_3525_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v___x_3525_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_snd_3523_);
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_snd_3523_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v_snd_3523_);
v_a_3534_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3525_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3525_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_snd_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3568_; 
lean_inc_ref(v_fst_3522_);
v_snd_3542_ = lean_ctor_get(v_a_3521_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_a_3521_, 0);
lean_dec(v_unused_3569_);
v___x_3544_ = v_a_3521_;
v_isShared_3545_ = v_isSharedCheck_3568_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_snd_3542_);
lean_dec(v_a_3521_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3568_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_val_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v_val_3546_ = lean_ctor_get(v_fst_3522_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_fst_3522_, 1);
v___x_3547_ = lean_box(0);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 1);
lean_ctor_set(v___x_3544_, 1, v___x_3547_);
lean_ctor_set(v___x_3544_, 0, v_val_3546_);
v___x_3549_ = v___x_3544_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_val_3546_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3549_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; 
v_unused_3558_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3558_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v_snd_3542_);
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_snd_3542_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_snd_3542_);
v_a_3559_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3550_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3550_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3520_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3520_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref(v_fvarIdsToSimp_3507_);
lean_dec_ref(v_simprocs_3506_);
lean_dec_ref(v_ctx_3505_);
v_a_3578_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3515_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3515_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3586_, lean_object* v_simprocs_3587_, lean_object* v_fvarIdsToSimp_3588_, lean_object* v_simplifyTarget_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
uint8_t v_simplifyTarget_boxed_3596_; lean_object* v_res_3597_; 
v_simplifyTarget_boxed_3596_ = lean_unbox(v_simplifyTarget_3589_);
v_res_3597_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3586_, v_simprocs_3587_, v_fvarIdsToSimp_3588_, v_simplifyTarget_boxed_3596_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3598_, lean_object* v_simprocs_3599_, lean_object* v_fvarIdsToSimp_3600_, uint8_t v_simplifyTarget_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3598_, v_simprocs_3599_, v_fvarIdsToSimp_3600_, v_simplifyTarget_3601_, v_a_3603_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3612_, lean_object* v_simprocs_3613_, lean_object* v_fvarIdsToSimp_3614_, lean_object* v_simplifyTarget_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
uint8_t v_simplifyTarget_boxed_3625_; lean_object* v_res_3626_; 
v_simplifyTarget_boxed_3625_ = lean_unbox(v_simplifyTarget_3615_);
v_res_3626_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3612_, v_simprocs_3613_, v_fvarIdsToSimp_3614_, v_simplifyTarget_boxed_3625_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3627_, lean_object* v_simprocs_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3630_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3640_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v___x_3640_ = l_Lean_MVarId_getNondepPropHyps(v_a_3639_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; uint8_t v___x_3642_; lean_object* v___x_3643_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v___x_3642_ = 1;
v___x_3643_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3627_, v_simprocs_3628_, v_a_3641_, v___x_3642_, v___y_3630_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
return v___x_3643_;
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref(v_simprocs_3628_);
lean_dec_ref(v_ctx_3627_);
v_a_3644_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3640_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec_ref(v_simprocs_3628_);
lean_dec_ref(v_ctx_3627_);
v_a_3652_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3638_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3638_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3660_, lean_object* v_simprocs_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3660_, v_simprocs_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3672_, lean_object* v_ctx_3673_, lean_object* v_simprocs_3674_, uint8_t v_type_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3672_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3673_, v_simprocs_3674_, v_a_3686_, v_type_3675_, v___y_3677_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
return v___x_3687_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_simprocs_3674_);
lean_dec_ref(v_ctx_3673_);
v_a_3688_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3685_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3685_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3696_, lean_object* v_ctx_3697_, lean_object* v_simprocs_3698_, lean_object* v_type_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_type_555__boxed_3709_; lean_object* v_res_3710_; 
v_type_555__boxed_3709_ = lean_unbox(v_type_3699_);
v_res_3710_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3696_, v_ctx_3697_, v_simprocs_3698_, v_type_555__boxed_3709_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3711_, lean_object* v_simprocs_3712_, lean_object* v_loc_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
if (lean_obj_tag(v_loc_3713_) == 0)
{
lean_object* v___f_3723_; lean_object* v___x_3724_; 
v___f_3723_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3723_, 0, v_ctx_3711_);
lean_closure_set(v___f_3723_, 1, v_simprocs_3712_);
v___x_3724_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3723_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
return v___x_3724_;
}
else
{
lean_object* v_hypotheses_3725_; uint8_t v_type_3726_; lean_object* v___x_3727_; lean_object* v___f_3728_; lean_object* v___x_3729_; 
v_hypotheses_3725_ = lean_ctor_get(v_loc_3713_, 0);
lean_inc_ref(v_hypotheses_3725_);
v_type_3726_ = lean_ctor_get_uint8(v_loc_3713_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3713_, 1);
v___x_3727_ = lean_box(v_type_3726_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3728_, 0, v_hypotheses_3725_);
lean_closure_set(v___f_3728_, 1, v_ctx_3711_);
lean_closure_set(v___f_3728_, 2, v_simprocs_3712_);
lean_closure_set(v___f_3728_, 3, v___x_3727_);
v___x_3729_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3728_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3730_, lean_object* v_simprocs_3731_, lean_object* v_loc_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3730_, v_simprocs_3731_, v_loc_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3747_, lean_object* v_stx_3748_, uint8_t v___x_3749_, lean_object* v___x_3750_, lean_object* v___x_3751_, lean_object* v___x_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
if (v___x_3747_ == 0)
{
lean_object* v___x_3762_; 
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_3762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; lean_object* v_tk_3764_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_stx_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v_args_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___x_4118_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v_o_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v_bang_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v___x_3763_ = lean_unsigned_to_nat(0u);
v_tk_3764_ = l_Lean_Syntax_getArg(v_stx_3748_, v___x_3763_);
v___x_4118_ = lean_unsigned_to_nat(1u);
v___x_4174_ = l_Lean_Syntax_getArg(v_stx_3748_, v___x_4118_);
v___x_4175_ = l_Lean_Syntax_isNone(v___x_4174_);
if (v___x_4175_ == 0)
{
uint8_t v___x_4176_; 
lean_inc(v___x_4174_);
v___x_4176_ = l_Lean_Syntax_matchesNull(v___x_4174_, v___x_4118_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; 
lean_dec(v___x_4174_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4177_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4177_;
}
else
{
lean_object* v_bang_4178_; lean_object* v___x_4179_; 
v_bang_4178_ = l_Lean_Syntax_getArg(v___x_4174_, v___x_3763_);
lean_dec(v___x_4174_);
v___x_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_bang_4178_);
v_bang_4147_ = v___x_4179_;
v___y_4148_ = v___y_3753_;
v___y_4149_ = v___y_3754_;
v___y_4150_ = v___y_3755_;
v___y_4151_ = v___y_3756_;
v___y_4152_ = v___y_3757_;
v___y_4153_ = v___y_3758_;
v___y_4154_ = v___y_3759_;
v___y_4155_ = v___y_3760_;
goto v___jp_4146_;
}
}
else
{
lean_object* v___x_4180_; 
lean_dec(v___x_4174_);
v___x_4180_ = lean_box(0);
v_bang_4147_ = v___x_4180_;
v___y_4148_ = v___y_3753_;
v___y_4149_ = v___y_3754_;
v___y_4150_ = v___y_3755_;
v___y_4151_ = v___y_3756_;
v___y_4152_ = v___y_3757_;
v___y_4153_ = v___y_3758_;
v___y_4154_ = v___y_3759_;
v___y_4155_ = v___y_3760_;
goto v___jp_4146_;
}
v___jp_3765_:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3767_, v___y_3770_, v___y_3777_, v___y_3772_, v___y_3769_, v___y_3773_, v___y_3776_, v___y_3771_, v___y_3774_, v___y_3766_, v___y_3768_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v_usedTheorems_3780_; lean_object* v_diag_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3823_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
v_usedTheorems_3780_ = lean_ctor_get(v_a_3779_, 0);
v_diag_3781_ = lean_ctor_get(v_a_3779_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_a_3779_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3783_ = v_a_3779_;
v_isShared_3784_ = v_isSharedCheck_3823_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_diag_3781_);
lean_inc(v_usedTheorems_3780_);
lean_dec(v_a_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3823_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3775_, v_usedTheorems_3780_, v___y_3771_, v___y_3774_, v___y_3766_, v___y_3768_);
lean_dec_ref(v_usedTheorems_3780_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v_ref_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v_ref_3787_ = lean_ctor_get(v___y_3766_, 2);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 1, v_a_3786_);
lean_ctor_set(v___x_3783_, 0, v___x_3788_);
v___x_3790_ = v___x_3783_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_a_3786_);
v___x_3790_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
lean_ctor_set(v___x_3792_, 2, v___x_3791_);
lean_ctor_set(v___x_3792_, 3, v___x_3791_);
lean_ctor_set(v___x_3792_, 4, v___x_3791_);
lean_ctor_set(v___x_3792_, 5, v___x_3791_);
lean_inc(v_ref_3787_);
v___x_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_ref_3787_);
v___x_3794_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3795_ = 4;
v___x_3796_ = l_Lean_MessageData_nil;
v___x_3797_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3764_, v___x_3792_, v___x_3793_, v___x_3794_, v___x_3791_, v___x_3795_, v___x_3796_, v___y_3766_, v___y_3768_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v___x_3797_, 0);
lean_dec(v_unused_3805_);
v___x_3799_ = v___x_3797_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v___x_3797_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_diag_3781_);
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_diag_3781_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_diag_3781_);
v_a_3806_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3797_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3797_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_del_object(v___x_3783_);
lean_dec_ref(v_diag_3781_);
lean_dec(v_tk_3764_);
v_a_3815_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3785_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3785_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v___y_3775_);
lean_dec(v_tk_3764_);
v_a_3824_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3778_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3778_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
v___jp_3832_:
{
if (lean_obj_tag(v___y_3841_) == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3846_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
lean_ctor_set_uint8(v___x_3846_, sizeof(void*)*1, v___x_3749_);
v___y_3766_ = v___y_3833_;
v___y_3767_ = v___y_3844_;
v___y_3768_ = v___y_3835_;
v___y_3769_ = v___y_3834_;
v___y_3770_ = v___y_3836_;
v___y_3771_ = v___y_3838_;
v___y_3772_ = v___y_3837_;
v___y_3773_ = v___y_3839_;
v___y_3774_ = v___y_3840_;
v___y_3775_ = v___y_3843_;
v___y_3776_ = v___y_3842_;
v___y_3777_ = v___x_3846_;
goto v___jp_3765_;
}
else
{
lean_object* v_val_3847_; lean_object* v___x_3848_; 
v_val_3847_ = lean_ctor_get(v___y_3841_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v___y_3841_, 1);
v___x_3848_ = l_Lean_Elab_Tactic_expandLocation(v_val_3847_);
lean_dec(v_val_3847_);
v___y_3766_ = v___y_3833_;
v___y_3767_ = v___y_3844_;
v___y_3768_ = v___y_3835_;
v___y_3769_ = v___y_3834_;
v___y_3770_ = v___y_3836_;
v___y_3771_ = v___y_3838_;
v___y_3772_ = v___y_3837_;
v___y_3773_ = v___y_3839_;
v___y_3774_ = v___y_3840_;
v___y_3775_ = v___y_3843_;
v___y_3776_ = v___y_3842_;
v___y_3777_ = v___x_3848_;
goto v___jp_3765_;
}
}
v___jp_3849_:
{
uint8_t v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3861_ = 0;
v___x_3862_ = 2;
v___x_3863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3864_ = lean_box(v___x_3861_);
v___x_3865_ = lean_box(v___x_3862_);
v___x_3866_ = lean_box(v___x_3861_);
lean_inc(v_stx_3852_);
v___x_3867_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3867_, 0, v_stx_3852_);
lean_closure_set(v___x_3867_, 1, v___x_3864_);
lean_closure_set(v___x_3867_, 2, v___x_3865_);
lean_closure_set(v___x_3867_, 3, v___x_3866_);
lean_closure_set(v___x_3867_, 4, v___x_3863_);
v___x_3868_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3867_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
if (lean_obj_tag(v___y_3850_) == 0)
{
lean_object* v_ctx_3870_; lean_object* v_simprocs_3871_; 
v_ctx_3870_ = lean_ctor_get(v_a_3869_, 0);
lean_inc_ref(v_ctx_3870_);
v_simprocs_3871_ = lean_ctor_get(v_a_3869_, 1);
lean_inc_ref(v_simprocs_3871_);
lean_dec(v_a_3869_);
v___y_3833_ = v___y_3859_;
v___y_3834_ = v___y_3854_;
v___y_3835_ = v___y_3860_;
v___y_3836_ = v_simprocs_3871_;
v___y_3837_ = v___y_3853_;
v___y_3838_ = v___y_3857_;
v___y_3839_ = v___y_3855_;
v___y_3840_ = v___y_3858_;
v___y_3841_ = v___y_3851_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v_stx_3852_;
v___y_3844_ = v_ctx_3870_;
goto v___jp_3832_;
}
else
{
lean_object* v_ctx_3872_; lean_object* v_simprocs_3873_; lean_object* v___x_3874_; 
lean_dec_ref_known(v___y_3850_, 1);
v_ctx_3872_ = lean_ctor_get(v_a_3869_, 0);
lean_inc_ref(v_ctx_3872_);
v_simprocs_3873_ = lean_ctor_get(v_a_3869_, 1);
lean_inc_ref(v_simprocs_3873_);
lean_dec(v_a_3869_);
v___x_3874_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3872_);
v___y_3833_ = v___y_3859_;
v___y_3834_ = v___y_3854_;
v___y_3835_ = v___y_3860_;
v___y_3836_ = v_simprocs_3873_;
v___y_3837_ = v___y_3853_;
v___y_3838_ = v___y_3857_;
v___y_3839_ = v___y_3855_;
v___y_3840_ = v___y_3858_;
v___y_3841_ = v___y_3851_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v_stx_3852_;
v___y_3844_ = v___x_3874_;
goto v___jp_3832_;
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_stx_3852_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v_tk_3764_);
v_a_3875_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3868_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3868_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
v___jp_3883_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_inc_ref(v___y_3888_);
v___x_3904_ = l_Array_append___redArg(v___y_3888_, v___y_3903_);
lean_dec_ref(v___y_3903_);
lean_inc(v___y_3896_);
lean_inc(v___y_3890_);
v___x_3905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3905_, 0, v___y_3890_);
lean_ctor_set(v___x_3905_, 1, v___y_3896_);
lean_ctor_set(v___x_3905_, 2, v___x_3904_);
v___x_3906_ = l_Lean_Syntax_node6(v___y_3890_, v___y_3901_, v___y_3893_, v___y_3887_, v___y_3895_, v___y_3885_, v___y_3897_, v___x_3905_);
v___y_3850_ = v___y_3892_;
v___y_3851_ = v___y_3891_;
v_stx_3852_ = v___x_3906_;
v___y_3853_ = v___y_3898_;
v___y_3854_ = v___y_3894_;
v___y_3855_ = v___y_3886_;
v___y_3856_ = v___y_3899_;
v___y_3857_ = v___y_3889_;
v___y_3858_ = v___y_3902_;
v___y_3859_ = v___y_3900_;
v___y_3860_ = v___y_3884_;
goto v___jp_3849_;
}
v___jp_3907_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
lean_inc_ref(v___y_3912_);
v___x_3927_ = l_Array_append___redArg(v___y_3912_, v___y_3926_);
lean_dec_ref(v___y_3926_);
lean_inc(v___y_3920_);
lean_inc(v___y_3914_);
v___x_3928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3928_, 0, v___y_3914_);
lean_ctor_set(v___x_3928_, 1, v___y_3920_);
lean_ctor_set(v___x_3928_, 2, v___x_3927_);
if (lean_obj_tag(v___y_3915_) == 0)
{
lean_object* v___x_3929_; 
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3884_ = v___y_3908_;
v___y_3885_ = v___y_3909_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3911_;
v___y_3888_ = v___y_3912_;
v___y_3889_ = v___y_3913_;
v___y_3890_ = v___y_3914_;
v___y_3891_ = v___y_3915_;
v___y_3892_ = v___y_3916_;
v___y_3893_ = v___y_3917_;
v___y_3894_ = v___y_3918_;
v___y_3895_ = v___y_3919_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___x_3928_;
v___y_3898_ = v___y_3921_;
v___y_3899_ = v___y_3922_;
v___y_3900_ = v___y_3924_;
v___y_3901_ = v___y_3923_;
v___y_3902_ = v___y_3925_;
v___y_3903_ = v___x_3929_;
goto v___jp_3883_;
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_val_3930_ = lean_ctor_get(v___y_3915_, 0);
v___x_3931_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_3930_);
v___x_3932_ = lean_array_push(v___x_3931_, v_val_3930_);
v___y_3884_ = v___y_3908_;
v___y_3885_ = v___y_3909_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3911_;
v___y_3888_ = v___y_3912_;
v___y_3889_ = v___y_3913_;
v___y_3890_ = v___y_3914_;
v___y_3891_ = v___y_3915_;
v___y_3892_ = v___y_3916_;
v___y_3893_ = v___y_3917_;
v___y_3894_ = v___y_3918_;
v___y_3895_ = v___y_3919_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___x_3928_;
v___y_3898_ = v___y_3921_;
v___y_3899_ = v___y_3922_;
v___y_3900_ = v___y_3924_;
v___y_3901_ = v___y_3923_;
v___y_3902_ = v___y_3925_;
v___y_3903_ = v___x_3932_;
goto v___jp_3883_;
}
}
v___jp_3933_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
lean_inc_ref(v___y_3937_);
v___x_3953_ = l_Array_append___redArg(v___y_3937_, v___y_3952_);
lean_dec_ref(v___y_3952_);
lean_inc(v___y_3946_);
lean_inc(v___y_3940_);
v___x_3954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3954_, 0, v___y_3940_);
lean_ctor_set(v___x_3954_, 1, v___y_3946_);
lean_ctor_set(v___x_3954_, 2, v___x_3953_);
if (lean_obj_tag(v___y_3938_) == 1)
{
lean_object* v_val_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_val_3955_ = lean_ctor_get(v___y_3938_, 0);
lean_inc(v_val_3955_);
lean_dec_ref_known(v___y_3938_, 1);
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_3940_, 3);
v___x_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___y_3940_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
lean_inc_ref(v___y_3937_);
v___x_3958_ = l_Array_append___redArg(v___y_3937_, v_val_3955_);
lean_dec(v_val_3955_);
lean_inc(v___y_3946_);
v___x_3959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___y_3940_);
lean_ctor_set(v___x_3959_, 1, v___y_3946_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___y_3940_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Array_mkArray3___redArg(v___x_3957_, v___x_3959_, v___x_3961_);
v___y_3908_ = v___y_3934_;
v___y_3909_ = v___x_3954_;
v___y_3910_ = v___y_3935_;
v___y_3911_ = v___y_3936_;
v___y_3912_ = v___y_3937_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3944_;
v___y_3919_ = v___y_3945_;
v___y_3920_ = v___y_3946_;
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3948_;
v___y_3923_ = v___y_3950_;
v___y_3924_ = v___y_3949_;
v___y_3925_ = v___y_3951_;
v___y_3926_ = v___x_3962_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3963_; 
lean_dec(v___y_3938_);
v___x_3963_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3908_ = v___y_3934_;
v___y_3909_ = v___x_3954_;
v___y_3910_ = v___y_3935_;
v___y_3911_ = v___y_3936_;
v___y_3912_ = v___y_3937_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3944_;
v___y_3919_ = v___y_3945_;
v___y_3920_ = v___y_3946_;
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3948_;
v___y_3923_ = v___y_3950_;
v___y_3924_ = v___y_3949_;
v___y_3925_ = v___y_3951_;
v___y_3926_ = v___x_3963_;
goto v___jp_3907_;
}
}
v___jp_3964_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_inc_ref(v___y_3982_);
v___x_3985_ = l_Array_append___redArg(v___y_3982_, v___y_3984_);
lean_dec_ref(v___y_3984_);
lean_inc(v___y_3967_);
lean_inc(v___y_3977_);
v___x_3986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3986_, 0, v___y_3977_);
lean_ctor_set(v___x_3986_, 1, v___y_3967_);
lean_ctor_set(v___x_3986_, 2, v___x_3985_);
v___x_3987_ = l_Lean_Syntax_node6(v___y_3977_, v___y_3971_, v___y_3965_, v___y_3969_, v___y_3972_, v___y_3973_, v___y_3983_, v___x_3986_);
v___y_3850_ = v___y_3975_;
v___y_3851_ = v___y_3974_;
v_stx_3852_ = v___x_3987_;
v___y_3853_ = v___y_3978_;
v___y_3854_ = v___y_3976_;
v___y_3855_ = v___y_3968_;
v___y_3856_ = v___y_3979_;
v___y_3857_ = v___y_3970_;
v___y_3858_ = v___y_3981_;
v___y_3859_ = v___y_3980_;
v___y_3860_ = v___y_3966_;
goto v___jp_3849_;
}
v___jp_3988_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_inc_ref(v___y_4006_);
v___x_4008_ = l_Array_append___redArg(v___y_4006_, v___y_4007_);
lean_dec_ref(v___y_4007_);
lean_inc(v___y_3991_);
lean_inc(v___y_4002_);
v___x_4009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4009_, 0, v___y_4002_);
lean_ctor_set(v___x_4009_, 1, v___y_3991_);
lean_ctor_set(v___x_4009_, 2, v___x_4008_);
if (lean_obj_tag(v___y_3998_) == 0)
{
lean_object* v___x_4010_; 
v___x_4010_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3965_ = v___y_3989_;
v___y_3966_ = v___y_3990_;
v___y_3967_ = v___y_3991_;
v___y_3968_ = v___y_3992_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
v___y_3977_ = v___y_4002_;
v___y_3978_ = v___y_4001_;
v___y_3979_ = v___y_4003_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v___y_4005_;
v___y_3982_ = v___y_4006_;
v___y_3983_ = v___x_4009_;
v___y_3984_ = v___x_4010_;
goto v___jp_3964_;
}
else
{
lean_object* v_val_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_val_4011_ = lean_ctor_get(v___y_3998_, 0);
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4011_);
v___x_4013_ = lean_array_push(v___x_4012_, v_val_4011_);
v___y_3965_ = v___y_3989_;
v___y_3966_ = v___y_3990_;
v___y_3967_ = v___y_3991_;
v___y_3968_ = v___y_3992_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
v___y_3977_ = v___y_4002_;
v___y_3978_ = v___y_4001_;
v___y_3979_ = v___y_4003_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v___y_4005_;
v___y_3982_ = v___y_4006_;
v___y_3983_ = v___x_4009_;
v___y_3984_ = v___x_4013_;
goto v___jp_3964_;
}
}
v___jp_4014_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_inc_ref(v___y_4032_);
v___x_4034_ = l_Array_append___redArg(v___y_4032_, v___y_4033_);
lean_dec_ref(v___y_4033_);
lean_inc(v___y_4017_);
lean_inc(v___y_4028_);
v___x_4035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4035_, 0, v___y_4028_);
lean_ctor_set(v___x_4035_, 1, v___y_4017_);
lean_ctor_set(v___x_4035_, 2, v___x_4034_);
if (lean_obj_tag(v___y_4020_) == 1)
{
lean_object* v_val_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_val_4036_ = lean_ctor_get(v___y_4020_, 0);
lean_inc(v_val_4036_);
lean_dec_ref_known(v___y_4020_, 1);
v___x_4037_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4028_, 3);
v___x_4038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___y_4028_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
lean_inc_ref(v___y_4032_);
v___x_4039_ = l_Array_append___redArg(v___y_4032_, v_val_4036_);
lean_dec(v_val_4036_);
lean_inc(v___y_4017_);
v___x_4040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4028_);
lean_ctor_set(v___x_4040_, 1, v___y_4017_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___y_4028_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Array_mkArray3___redArg(v___x_4038_, v___x_4040_, v___x_4042_);
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4016_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___y_4018_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___x_4035_;
v___y_3998_ = v___y_4024_;
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4026_;
v___y_4001_ = v___y_4027_;
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4032_;
v___y_4007_ = v___x_4043_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4044_; 
lean_dec(v___y_4020_);
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4016_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___y_4018_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___x_4035_;
v___y_3998_ = v___y_4024_;
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4026_;
v___y_4001_ = v___y_4027_;
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4032_;
v___y_4007_ = v___x_4044_;
goto v___jp_3988_;
}
}
v___jp_4045_:
{
if (lean_obj_tag(v___y_4052_) == 0)
{
lean_object* v_ref_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v_ref_4059_ = lean_ctor_get(v___y_4056_, 2);
v___x_4060_ = 0;
v___x_4061_ = l_Lean_SourceInfo_fromRef(v_ref_4059_, v___x_4060_);
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4063_ = l_Lean_Name_mkStr4(v___x_3750_, v___x_3751_, v___x_3752_, v___x_4062_);
v___x_4064_ = l_Lean_SourceInfo_fromRef(v_tk_3764_, v___x_3749_);
v___x_4065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___x_4062_);
v___x_4066_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4067_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4061_);
v___x_4068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4061_);
lean_ctor_set(v___x_4068_, 1, v___x_4066_);
lean_ctor_set(v___x_4068_, 2, v___x_4067_);
if (lean_obj_tag(v___y_4048_) == 1)
{
lean_object* v_val_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_val_4069_ = lean_ctor_get(v___y_4048_, 0);
lean_inc(v_val_4069_);
lean_dec_ref_known(v___y_4048_, 1);
v___x_4070_ = l_Lean_SourceInfo_fromRef(v_val_4069_, v___x_3749_);
lean_dec(v_val_4069_);
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Array_mkArray1___redArg(v___x_4072_);
v___y_3934_ = v___y_4046_;
v___y_3935_ = v___y_4047_;
v___y_3936_ = v___y_4049_;
v___y_3937_ = v___x_4067_;
v___y_3938_ = v___y_4050_;
v___y_3939_ = v___y_4051_;
v___y_3940_ = v___x_4061_;
v___y_3941_ = v___y_4058_;
v___y_3942_ = v___y_4052_;
v___y_3943_ = v___x_4065_;
v___y_3944_ = v___y_4053_;
v___y_3945_ = v___x_4068_;
v___y_3946_ = v___x_4066_;
v___y_3947_ = v___y_4054_;
v___y_3948_ = v___y_4055_;
v___y_3949_ = v___y_4056_;
v___y_3950_ = v___x_4063_;
v___y_3951_ = v___y_4057_;
v___y_3952_ = v___x_4073_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_4074_; 
lean_dec(v___y_4048_);
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3934_ = v___y_4046_;
v___y_3935_ = v___y_4047_;
v___y_3936_ = v___y_4049_;
v___y_3937_ = v___x_4067_;
v___y_3938_ = v___y_4050_;
v___y_3939_ = v___y_4051_;
v___y_3940_ = v___x_4061_;
v___y_3941_ = v___y_4058_;
v___y_3942_ = v___y_4052_;
v___y_3943_ = v___x_4065_;
v___y_3944_ = v___y_4053_;
v___y_3945_ = v___x_4068_;
v___y_3946_ = v___x_4066_;
v___y_3947_ = v___y_4054_;
v___y_3948_ = v___y_4055_;
v___y_3949_ = v___y_4056_;
v___y_3950_ = v___x_4063_;
v___y_3951_ = v___y_4057_;
v___y_3952_ = v___x_4074_;
goto v___jp_3933_;
}
}
else
{
lean_object* v_ref_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v_ref_4075_ = lean_ctor_get(v___y_4056_, 2);
v___x_4076_ = 0;
v___x_4077_ = l_Lean_SourceInfo_fromRef(v_ref_4075_, v___x_4076_);
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4079_ = l_Lean_Name_mkStr4(v___x_3750_, v___x_3751_, v___x_3752_, v___x_4078_);
v___x_4080_ = l_Lean_SourceInfo_fromRef(v_tk_3764_, v___x_3749_);
v___x_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4084_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4077_);
v___x_4085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4077_);
lean_ctor_set(v___x_4085_, 1, v___x_4083_);
lean_ctor_set(v___x_4085_, 2, v___x_4084_);
if (lean_obj_tag(v___y_4048_) == 1)
{
lean_object* v_val_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_val_4086_ = lean_ctor_get(v___y_4048_, 0);
lean_inc(v_val_4086_);
lean_dec_ref_known(v___y_4048_, 1);
v___x_4087_ = l_Lean_SourceInfo_fromRef(v_val_4086_, v___x_3749_);
lean_dec(v_val_4086_);
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Array_mkArray1___redArg(v___x_4089_);
v___y_4015_ = v___x_4082_;
v___y_4016_ = v___y_4046_;
v___y_4017_ = v___x_4083_;
v___y_4018_ = v___y_4047_;
v___y_4019_ = v___y_4049_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___y_4051_;
v___y_4022_ = v___x_4079_;
v___y_4023_ = v___x_4085_;
v___y_4024_ = v___y_4058_;
v___y_4025_ = v___y_4052_;
v___y_4026_ = v___y_4053_;
v___y_4027_ = v___y_4054_;
v___y_4028_ = v___x_4077_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4056_;
v___y_4031_ = v___y_4057_;
v___y_4032_ = v___x_4084_;
v___y_4033_ = v___x_4090_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4091_; 
lean_dec(v___y_4048_);
v___x_4091_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4015_ = v___x_4082_;
v___y_4016_ = v___y_4046_;
v___y_4017_ = v___x_4083_;
v___y_4018_ = v___y_4047_;
v___y_4019_ = v___y_4049_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___y_4051_;
v___y_4022_ = v___x_4079_;
v___y_4023_ = v___x_4085_;
v___y_4024_ = v___y_4058_;
v___y_4025_ = v___y_4052_;
v___y_4026_ = v___y_4053_;
v___y_4027_ = v___y_4054_;
v___y_4028_ = v___x_4077_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4056_;
v___y_4031_ = v___y_4057_;
v___y_4032_ = v___x_4084_;
v___y_4033_ = v___x_4091_;
goto v___jp_4014_;
}
}
}
v___jp_4092_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = lean_unsigned_to_nat(3u);
v___x_4107_ = l_Lean_Syntax_getArg(v___y_4096_, v___x_4106_);
lean_dec(v___y_4096_);
v___x_4108_ = l_Lean_Syntax_getOptional_x3f(v___x_4107_);
lean_dec(v___x_4107_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_box(0);
v___y_4046_ = v___y_4105_;
v___y_4047_ = v___y_4100_;
v___y_4048_ = v___y_4094_;
v___y_4049_ = v___y_4095_;
v___y_4050_ = v_args_4097_;
v___y_4051_ = v___y_4102_;
v___y_4052_ = v___y_4093_;
v___y_4053_ = v___y_4099_;
v___y_4054_ = v___y_4098_;
v___y_4055_ = v___y_4101_;
v___y_4056_ = v___y_4104_;
v___y_4057_ = v___y_4103_;
v___y_4058_ = v___x_4109_;
goto v___jp_4045_;
}
else
{
lean_object* v_val_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_val_4110_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4108_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_val_4110_);
lean_dec(v___x_4108_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_val_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
v___y_4046_ = v___y_4105_;
v___y_4047_ = v___y_4100_;
v___y_4048_ = v___y_4094_;
v___y_4049_ = v___y_4095_;
v___y_4050_ = v_args_4097_;
v___y_4051_ = v___y_4102_;
v___y_4052_ = v___y_4093_;
v___y_4053_ = v___y_4099_;
v___y_4054_ = v___y_4098_;
v___y_4055_ = v___y_4101_;
v___y_4056_ = v___y_4104_;
v___y_4057_ = v___y_4103_;
v___y_4058_ = v___x_4115_;
goto v___jp_4045_;
}
}
}
}
v___jp_4119_:
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = l_Lean_Syntax_getArg(v___y_4123_, v___y_4122_);
v___x_4134_ = l_Lean_Syntax_isNone(v___x_4133_);
if (v___x_4134_ == 0)
{
uint8_t v___x_4135_; 
lean_inc(v___x_4133_);
v___x_4135_ = l_Lean_Syntax_matchesNull(v___x_4133_, v___x_4118_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; 
lean_dec(v___x_4133_);
lean_dec(v_o_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4136_;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4137_ = l_Lean_Syntax_getArg(v___x_4133_, v___x_3763_);
lean_dec(v___x_4133_);
v___x_4138_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3752_);
lean_inc_ref(v___x_3751_);
lean_inc_ref(v___x_3750_);
v___x_4139_ = l_Lean_Name_mkStr4(v___x_3750_, v___x_3751_, v___x_3752_, v___x_4138_);
lean_inc(v___x_4137_);
v___x_4140_ = l_Lean_Syntax_isOfKind(v___x_4137_, v___x_4139_);
lean_dec(v___x_4139_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_dec(v___x_4137_);
lean_dec(v_o_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4141_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4141_;
}
else
{
lean_object* v___x_4142_; lean_object* v_args_4143_; lean_object* v___x_4144_; 
v___x_4142_ = l_Lean_Syntax_getArg(v___x_4137_, v___x_4118_);
lean_dec(v___x_4137_);
v_args_4143_ = l_Lean_Syntax_getArgs(v___x_4142_);
lean_dec(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4144_, 0, v_args_4143_);
v___y_4093_ = v___y_4120_;
v___y_4094_ = v_o_4124_;
v___y_4095_ = v___y_4121_;
v___y_4096_ = v___y_4123_;
v_args_4097_ = v___x_4144_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
goto v___jp_4092_;
}
}
}
else
{
lean_object* v___x_4145_; 
lean_dec(v___x_4133_);
v___x_4145_ = lean_box(0);
v___y_4093_ = v___y_4120_;
v___y_4094_ = v_o_4124_;
v___y_4095_ = v___y_4121_;
v___y_4096_ = v___y_4123_;
v_args_4097_ = v___x_4145_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
goto v___jp_4092_;
}
}
v___jp_4146_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; uint8_t v___x_4160_; 
v___x_4156_ = lean_unsigned_to_nat(2u);
v___x_4157_ = l_Lean_Syntax_getArg(v_stx_3748_, v___x_4156_);
v___x_4158_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3752_);
lean_inc_ref(v___x_3751_);
lean_inc_ref(v___x_3750_);
v___x_4159_ = l_Lean_Name_mkStr4(v___x_3750_, v___x_3751_, v___x_3752_, v___x_4158_);
lean_inc(v___x_4157_);
v___x_4160_ = l_Lean_Syntax_isOfKind(v___x_4157_, v___x_4159_);
lean_dec(v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; 
lean_dec(v___x_4157_);
lean_dec(v_bang_4147_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4162_ = l_Lean_Syntax_getArg(v___x_4157_, v___x_3763_);
v___x_4163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3752_);
lean_inc_ref(v___x_3751_);
lean_inc_ref(v___x_3750_);
v___x_4164_ = l_Lean_Name_mkStr4(v___x_3750_, v___x_3751_, v___x_3752_, v___x_4163_);
lean_inc(v___x_4162_);
v___x_4165_ = l_Lean_Syntax_isOfKind(v___x_4162_, v___x_4164_);
lean_dec(v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v___x_4162_);
lean_dec(v___x_4157_);
lean_dec(v_bang_4147_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4166_;
}
else
{
lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4167_ = l_Lean_Syntax_getArg(v___x_4157_, v___x_4118_);
v___x_4168_ = l_Lean_Syntax_isNone(v___x_4167_);
if (v___x_4168_ == 0)
{
uint8_t v___x_4169_; 
lean_inc(v___x_4167_);
v___x_4169_ = l_Lean_Syntax_matchesNull(v___x_4167_, v___x_4118_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; 
lean_dec(v___x_4167_);
lean_dec(v___x_4162_);
lean_dec(v___x_4157_);
lean_dec(v_bang_4147_);
lean_dec(v_tk_3764_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___x_3751_);
lean_dec_ref(v___x_3750_);
v___x_4170_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4170_;
}
else
{
lean_object* v_o_4171_; lean_object* v___x_4172_; 
v_o_4171_ = l_Lean_Syntax_getArg(v___x_4167_, v___x_3763_);
lean_dec(v___x_4167_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_o_4171_);
v___y_4120_ = v_bang_4147_;
v___y_4121_ = v___x_4162_;
v___y_4122_ = v___x_4156_;
v___y_4123_ = v___x_4157_;
v_o_4124_ = v___x_4172_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4149_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4151_;
v___y_4129_ = v___y_4152_;
v___y_4130_ = v___y_4153_;
v___y_4131_ = v___y_4154_;
v___y_4132_ = v___y_4155_;
goto v___jp_4119_;
}
}
else
{
lean_object* v___x_4173_; 
lean_dec(v___x_4167_);
v___x_4173_ = lean_box(0);
v___y_4120_ = v_bang_4147_;
v___y_4121_ = v___x_4162_;
v___y_4122_ = v___x_4156_;
v___y_4123_ = v___x_4157_;
v_o_4124_ = v___x_4173_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4149_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4151_;
v___y_4129_ = v___y_4152_;
v___y_4130_ = v___y_4153_;
v___y_4131_ = v___y_4154_;
v___y_4132_ = v___y_4155_;
goto v___jp_4119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4181_, lean_object* v_stx_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v___x_8015__boxed_4196_; uint8_t v___x_8016__boxed_4197_; lean_object* v_res_4198_; 
v___x_8015__boxed_4196_ = lean_unbox(v___x_4181_);
v___x_8016__boxed_4197_ = lean_unbox(v___x_4183_);
v_res_4198_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8015__boxed_4196_, v_stx_4182_, v___x_8016__boxed_4197_, v___x_4184_, v___x_4185_, v___x_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v_stx_4182_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___y_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4218_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4205_);
v___x_4219_ = l_Lean_Syntax_isOfKind(v_stx_4205_, v___x_4218_);
v___x_4220_ = 1;
v___x_4221_ = lean_box(v___x_4219_);
v___x_4222_ = lean_box(v___x_4220_);
v___y_4223_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4223_, 0, v___x_4221_);
lean_closure_set(v___y_4223_, 1, v_stx_4205_);
lean_closure_set(v___y_4223_, 2, v___x_4222_);
lean_closure_set(v___y_4223_, 3, v___x_4215_);
lean_closure_set(v___y_4223_, 4, v___x_4216_);
lean_closure_set(v___y_4223_, 5, v___x_4217_);
v___x_4224_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4224_, 0, v___y_4223_);
v___x_4225_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4224_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
lean_dec(v_a_4228_);
lean_dec_ref(v_a_4227_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4244_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4247_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4248_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4244_, v___x_4245_, v___x_4246_, v___x_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4279_ = l_Lean_addBuiltinDeclarationRanges(v___x_4277_, v___x_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4281_;
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
