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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27;
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
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v_pre_49_);
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
uint8_t v___x_33627__boxed_204_; lean_object* v_res_205_; 
v___x_33627__boxed_204_ = lean_unbox(v___x_197_);
v_res_205_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33627__boxed_204_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
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
uint8_t v___x_33654__boxed_242_; lean_object* v_res_243_; 
v___x_33654__boxed_242_ = lean_unbox(v___x_229_);
v_res_243_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_227_, v___x_228_, v___x_33654__boxed_242_, v___y_230_, v_simprocs_231_, v_discharge_x3f_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
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
lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; uint8_t v___y_397_; lean_object* v___y_398_; uint8_t v___y_399_; lean_object* v___y_400_; lean_object* v_toCold_401_; lean_object* v___y_402_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; uint8_t v___y_435_; lean_object* v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; uint8_t v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; uint8_t v___y_468_; uint8_t v___y_469_; uint8_t v___x_479_; uint8_t v___y_481_; uint8_t v___x_487_; 
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
lean_ctor_set(v___x_406_, 1, v___y_398_);
lean_inc_ref(v___y_395_);
lean_inc_ref(v___y_400_);
v___x_407_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_407_, 0, v___y_400_);
lean_ctor_set(v___x_407_, 1, v___y_396_);
lean_ctor_set(v___x_407_, 2, v___y_394_);
lean_ctor_set(v___x_407_, 3, v___y_395_);
lean_ctor_set(v___x_407_, 4, v___x_406_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5, v___y_397_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5 + 1, v___y_399_);
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
v_fileName_439_ = lean_ctor_get(v___y_433_, 0);
v_fileMap_440_ = lean_ctor_get(v___y_433_, 1);
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
v___x_447_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_436_);
lean_dec(v___y_436_);
v___x_448_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_438_);
lean_dec(v___y_438_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_435_ == 0)
{
lean_del_object(v___x_445_);
lean_dec_ref(v___y_431_);
v___y_394_ = v___x_449_;
v___y_395_ = v___x_450_;
v___y_396_ = v___x_447_;
v___y_397_ = v___y_434_;
v___y_398_ = v_a_443_;
v___y_399_ = v___y_437_;
v___y_400_ = v_fileName_439_;
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
v___y_394_ = v___x_449_;
v___y_395_ = v___x_450_;
v___y_396_ = v___x_447_;
v___y_397_ = v___y_434_;
v___y_398_ = v_a_443_;
v___y_399_ = v___y_437_;
v___y_400_ = v_fileName_439_;
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
v___x_465_ = l_Lean_Syntax_getTailPos_x3f(v___y_463_, v___y_461_);
lean_dec(v___y_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_inc(v___y_464_);
v___y_431_ = v___y_458_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_459_;
v___y_434_ = v___y_461_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_464_;
v___y_437_ = v___y_462_;
v___y_438_ = v___y_464_;
goto v___jp_430_;
}
else
{
lean_object* v_val_466_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___y_431_ = v___y_458_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_459_;
v___y_434_ = v___y_461_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_464_;
v___y_437_ = v___y_462_;
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
v___y_458_ = v___f_474_;
v___y_459_ = v_toCold_470_;
v___y_460_ = v_suppressElabErrors_472_;
v___y_461_ = v___y_468_;
v___y_462_ = v___y_469_;
v___y_463_ = v_ref_475_;
v___y_464_ = v___x_477_;
goto v___jp_457_;
}
else
{
lean_object* v_val_478_; 
v_val_478_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_476_, 1);
v___y_458_ = v___f_474_;
v___y_459_ = v_toCold_470_;
v___y_460_ = v_suppressElabErrors_472_;
v___y_461_ = v___y_468_;
v___y_462_ = v___y_469_;
v___y_463_ = v_ref_475_;
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
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
lean_ctor_set(v___x_756_, 3, v___x_755_);
lean_ctor_set(v___x_756_, 4, v___x_754_);
lean_ctor_set(v___x_756_, 5, v___x_754_);
lean_ctor_set(v___x_756_, 6, v___x_754_);
lean_ctor_set(v___x_756_, 7, v___x_754_);
lean_ctor_set(v___x_756_, 8, v___x_754_);
lean_ctor_set(v___x_756_, 9, v___x_754_);
lean_ctor_set(v___x_756_, 10, v___x_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_unsigned_to_nat(32u);
v___x_758_ = lean_mk_empty_array_with_capacity(v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = ((size_t)5ULL);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_unsigned_to_nat(32u);
v___x_763_ = lean_mk_empty_array_with_capacity(v___x_762_);
v___x_764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_765_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
lean_ctor_set(v___x_765_, 2, v___x_761_);
lean_ctor_set(v___x_765_, 3, v___x_761_);
lean_ctor_set_usize(v___x_765_, 4, v___x_760_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_box(1);
v___x_767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
lean_ctor_set(v___x_769_, 2, v___x_766_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_803_, lean_object* v_declHint_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_env_809_; uint8_t v___x_810_; 
v___x_807_ = lean_box(0);
v___x_808_ = lean_st_ref_get(v___y_805_);
v_env_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_env_809_);
lean_dec(v___x_808_);
v___x_810_ = l_Lean_Name_isAnonymous(v_declHint_804_);
if (v___x_810_ == 0)
{
uint8_t v_isExporting_811_; 
v_isExporting_811_ = lean_ctor_get_uint8(v_env_809_, sizeof(void*)*13);
if (v_isExporting_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v_env_809_);
lean_dec(v_declHint_804_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_msg_803_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
lean_inc_ref(v_env_809_);
v___x_813_ = l_Lean_Environment_setExporting(v_env_809_, v___x_810_);
lean_inc(v_declHint_804_);
lean_inc_ref(v___x_813_);
v___x_814_ = l_Lean_Environment_contains(v___x_813_, v_declHint_804_, v_isExporting_811_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec_ref(v___x_813_);
lean_dec_ref(v_env_809_);
lean_dec(v_declHint_804_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_msg_803_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_c_821_; lean_object* v___x_822_; 
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_818_ = l_Lean_Options_empty;
lean_inc_ref(v___x_813_);
v___x_819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_819_, 0, v___x_813_);
lean_ctor_set(v___x_819_, 1, v___x_816_);
lean_ctor_set(v___x_819_, 2, v___x_817_);
lean_ctor_set(v___x_819_, 3, v___x_818_);
lean_inc(v_declHint_804_);
v___x_820_ = l_Lean_MessageData_ofConstName(v_declHint_804_, v___x_810_);
v_c_821_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_821_, 0, v___x_819_);
lean_ctor_set(v_c_821_, 1, v___x_820_);
v___x_822_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_813_, v_declHint_804_);
lean_dec_ref(v___x_813_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v_env_809_);
lean_dec(v_declHint_804_);
v___x_823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_c_821_);
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_MessageData_note(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v_msg_803_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_883_; 
v_val_830_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_883_ == 0)
{
v___x_832_ = v___x_822_;
v_isShared_833_ = v_isSharedCheck_883_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_val_830_);
lean_dec(v___x_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_883_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_modules_835_; lean_object* v_moduleNames_836_; lean_object* v_mod_837_; uint8_t v___x_852_; 
v___x_834_ = l_Lean_Environment_header(v_env_809_);
lean_dec_ref(v_env_809_);
v_modules_835_ = lean_ctor_get(v___x_834_, 3);
lean_inc_ref(v_modules_835_);
v_moduleNames_836_ = lean_ctor_get(v___x_834_, 4);
lean_inc_ref(v_moduleNames_836_);
lean_dec_ref(v___x_834_);
v_mod_837_ = lean_array_get(v___x_807_, v_moduleNames_836_, v_val_830_);
lean_dec_ref(v_moduleNames_836_);
v___x_852_ = l_Lean_isPrivateName(v_declHint_804_);
lean_dec(v_declHint_804_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_array_get_size(v_modules_835_);
v___x_854_ = lean_nat_dec_lt(v_val_830_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec_ref(v_modules_835_);
lean_dec(v_val_830_);
goto v___jp_838_;
}
else
{
lean_object* v___x_855_; lean_object* v_toImport_856_; uint8_t v_isExported_857_; 
v___x_855_ = lean_array_fget(v_modules_835_, v_val_830_);
lean_dec(v_val_830_);
lean_dec_ref(v_modules_835_);
v_toImport_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_ref(v_toImport_856_);
lean_dec(v___x_855_);
v_isExported_857_ = lean_ctor_get_uint8(v_toImport_856_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_856_);
if (v_isExported_857_ == 0)
{
goto v___jp_838_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_del_object(v___x_832_);
v___x_858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_c_821_);
v___x_860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_MessageData_ofName(v_mod_837_);
lean_inc_ref(v___x_862_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_862_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_note(v___x_868_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v_msg_803_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_modules_835_);
lean_del_object(v___x_832_);
lean_dec(v_val_830_);
v___x_872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_c_821_);
v___x_874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_MessageData_ofName(v_mod_837_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_MessageData_note(v___x_879_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v_msg_803_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
v___jp_838_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_c_821_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_MessageData_ofName(v_mod_837_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Lean_MessageData_note(v___x_846_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v_msg_803_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 0);
lean_ctor_set(v___x_832_, 0, v___x_848_);
v___x_850_ = v___x_832_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v_env_809_);
lean_dec(v_declHint_804_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_msg_803_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_885_, lean_object* v_declHint_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_885_, v_declHint_886_, v___y_887_);
lean_dec(v___y_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_911_; 
v___x_901_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_890_, v_declHint_891_, v___y_899_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_911_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = l_Lean_unknownIdentifierMessageTag;
v___x_907_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v_a_902_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_912_, lean_object* v_declHint_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_912_, v_declHint_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_924_, lean_object* v_msg_925_, lean_object* v_declHint_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v_a_937_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_925_, v_declHint_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_924_, v_a_937_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_939_, lean_object* v_msg_940_, lean_object* v_declHint_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_939_, v_msg_940_, v_declHint_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_ref_939_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_958_, lean_object* v_constName_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_969_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_970_ = 0;
lean_inc(v_constName_959_);
v___x_971_ = l_Lean_MessageData_ofConstName(v_constName_959_, v___x_970_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_969_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_958_, v___x_974_, v_constName_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_976_, lean_object* v_constName_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_976_, v_constName_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v_ref_976_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_988_, lean_object* v_cs_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v_cs_1000_; uint8_t v___x_1004_; 
v___x_999_ = lean_box(0);
v_cs_1000_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_989_, v___x_999_);
v___x_1004_ = l_List_isEmpty___redArg(v_cs_1000_);
if (v___x_1004_ == 0)
{
lean_dec(v_n_988_);
goto v___jp_1001_;
}
else
{
lean_object* v_ref_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_cs_1000_);
v_ref_1005_ = lean_ctor_get(v___y_996_, 2);
v___x_1006_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_1005_, v_n_988_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
v___jp_1001_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_1000_, v___x_999_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1015_, lean_object* v_cs_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1015_, v_cs_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = 1;
lean_inc(v_n_1027_);
v___x_1038_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1027_, v___x_1037_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1027_, v_a_1039_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1040_;
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_n_1027_);
v_a_1041_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1038_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_array_to_list(v_a_1061_);
return v___x_1062_;
}
else
{
lean_object* v_head_1063_; 
v_head_1063_ = lean_ctor_get(v_a_1060_, 0);
if (lean_obj_tag(v_head_1063_) == 1)
{
lean_object* v_fields_1064_; 
v_fields_1064_ = lean_ctor_get(v_head_1063_, 1);
if (lean_obj_tag(v_fields_1064_) == 0)
{
lean_object* v_tail_1065_; lean_object* v_n_1066_; lean_object* v___x_1067_; 
lean_inc_ref(v_head_1063_);
v_tail_1065_ = lean_ctor_get(v_a_1060_, 1);
lean_inc(v_tail_1065_);
lean_dec_ref_known(v_a_1060_, 2);
v_n_1066_ = lean_ctor_get(v_head_1063_, 0);
lean_inc(v_n_1066_);
lean_dec_ref_known(v_head_1063_, 2);
v___x_1067_ = lean_array_push(v_a_1061_, v_n_1066_);
v_a_1060_ = v_tail_1065_;
v_a_1061_ = v___x_1067_;
goto _start;
}
else
{
lean_object* v_tail_1069_; 
v_tail_1069_ = lean_ctor_get(v_a_1060_, 1);
lean_inc(v_tail_1069_);
lean_dec_ref_known(v_a_1060_, 2);
v_a_1060_ = v_tail_1069_;
goto _start;
}
}
else
{
lean_object* v_tail_1071_; 
v_tail_1071_ = lean_ctor_get(v_a_1060_, 1);
lean_inc(v_tail_1071_);
lean_dec_ref_known(v_a_1060_, 2);
v_a_1060_ = v_tail_1071_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1079_ = l_Lean_MessageData_ofFormat(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1080_, lean_object* v_k_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
if (lean_obj_tag(v_stx_1080_) == 3)
{
lean_object* v_val_1091_; lean_object* v_preresolved_1092_; lean_object* v___x_1093_; lean_object* v_pre_1094_; uint8_t v___x_1095_; 
v_val_1091_ = lean_ctor_get(v_stx_1080_, 2);
lean_inc(v_val_1091_);
v_preresolved_1092_ = lean_ctor_get(v_stx_1080_, 3);
v___x_1093_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1092_);
v_pre_1094_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1092_, v___x_1093_);
v___x_1095_ = l_List_isEmpty___redArg(v_pre_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref_known(v_stx_1080_, 4);
lean_dec(v_val_1091_);
lean_dec_ref(v_k_1081_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_pre_1094_);
return v___x_1096_;
}
else
{
lean_object* v_toCold_1097_; lean_object* v_currRecDepth_1098_; lean_object* v_ref_1099_; uint16_t v_optionFlags_1100_; uint8_t v_suppressElabErrors_1101_; uint8_t v_checkDeprecated_1102_; uint8_t v_isRecordingDeps_1103_; lean_object* v_ref_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_pre_1094_);
v_toCold_1097_ = lean_ctor_get(v___y_1088_, 0);
v_currRecDepth_1098_ = lean_ctor_get(v___y_1088_, 1);
v_ref_1099_ = lean_ctor_get(v___y_1088_, 2);
v_optionFlags_1100_ = lean_ctor_get_uint16(v___y_1088_, sizeof(void*)*3);
v_suppressElabErrors_1101_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 2);
v_checkDeprecated_1102_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1103_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 4);
v_ref_1104_ = l_Lean_replaceRef(v_stx_1080_, v_ref_1099_);
lean_dec_ref_known(v_stx_1080_, 4);
lean_inc(v_currRecDepth_1098_);
lean_inc_ref(v_toCold_1097_);
v___x_1105_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1105_, 0, v_toCold_1097_);
lean_ctor_set(v___x_1105_, 1, v_currRecDepth_1098_);
lean_ctor_set(v___x_1105_, 2, v_ref_1104_);
lean_ctor_set_uint16(v___x_1105_, sizeof(void*)*3, v_optionFlags_1100_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3 + 2, v_suppressElabErrors_1101_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3 + 3, v_checkDeprecated_1102_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3 + 4, v_isRecordingDeps_1103_);
lean_inc(v___y_1089_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1106_ = lean_apply_10(v_k_1081_, v_val_1091_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___x_1105_, v___y_1089_, lean_box(0));
return v___x_1106_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_k_1081_);
v___x_1107_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1108_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1080_, v___x_1107_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v_stx_1080_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1109_, lean_object* v_k_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1109_, v_k_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1133_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1122_, v___x_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1148_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v_name_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1160_ = lean_array_uget_borrowed(v_as_1145_, v_i_1147_);
v_name_1161_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_name_1161_);
v___x_1162_ = l_Lean_mkIdent(v_name_1161_);
lean_inc(v___x_1162_);
v___x_1163_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1162_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1162_, v_a_1164_, v_b_1148_, v___y_1155_);
lean_dec(v_a_1164_);
lean_dec(v___x_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; size_t v___x_1167_; size_t v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1147_, v___x_1167_);
v_i_1147_ = v___x_1168_;
v_b_1148_ = v_a_1166_;
goto _start;
}
else
{
return v___x_1165_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v___x_1162_);
lean_dec_ref(v_b_1148_);
v_a_1170_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1163_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1163_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1178_, lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1178_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec_ref(v_as_1178_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1213_, lean_object* v_stx_1214_, uint8_t v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___f_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
if (v___x_1213_ == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_1229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v_tk_1231_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v_stxForSuggestion_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1493_; lean_object* v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1524_; uint8_t v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v_stxForExecution_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1637_; lean_object* v___y_1638_; uint8_t v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1668_; uint8_t v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1697_; uint8_t v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1766_; uint8_t v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v_argsArray_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_args_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___x_1966_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v_o_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v_bang_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v_tk_1231_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_1230_);
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_2024_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_1966_);
v___x_2025_ = l_Lean_Syntax_isNone(v___x_2024_);
if (v___x_2025_ == 0)
{
uint8_t v___x_2026_; 
lean_inc(v___x_2024_);
v___x_2026_ = l_Lean_Syntax_matchesNull(v___x_2024_, v___x_1966_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v___x_2024_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2027_;
}
else
{
lean_object* v_bang_2028_; lean_object* v___x_2029_; 
v_bang_2028_ = l_Lean_Syntax_getArg(v___x_2024_, v___x_1230_);
lean_dec(v___x_2024_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_bang_2028_);
v_bang_1996_ = v___x_2029_;
v___y_1997_ = v___y_1220_;
v___y_1998_ = v___y_1221_;
v___y_1999_ = v___y_1222_;
v___y_2000_ = v___y_1223_;
v___y_2001_ = v___y_1224_;
v___y_2002_ = v___y_1225_;
v___y_2003_ = v___y_1226_;
v___y_2004_ = v___y_1227_;
goto v___jp_1995_;
}
}
else
{
lean_object* v___x_2030_; 
lean_dec(v___x_2024_);
v___x_2030_ = lean_box(0);
v_bang_1996_ = v___x_2030_;
v___y_1997_ = v___y_1220_;
v___y_1998_ = v___y_1221_;
v___y_1999_ = v___y_1222_;
v___y_2000_ = v___y_1223_;
v___y_2001_ = v___y_1224_;
v___y_2002_ = v___y_1225_;
v___y_2003_ = v___y_1226_;
v___y_2004_ = v___y_1227_;
goto v___jp_1995_;
}
v___jp_1232_:
{
lean_object* v___x_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_box(v___x_1215_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1247_, 0, v___y_1234_);
lean_closure_set(v___f_1247_, 1, v___x_1230_);
lean_closure_set(v___f_1247_, 2, v___x_1246_);
lean_closure_set(v___f_1247_, 3, v___y_1245_);
lean_closure_set(v___f_1247_, 4, v___y_1235_);
v___x_1248_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1233_, v___f_1247_, v___y_1241_, v___y_1244_, v___y_1238_, v___y_1243_, v___y_1242_, v___y_1239_, v___y_1237_, v___y_1240_);
lean_dec(v___y_1233_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_usedTheorems_1250_; lean_object* v_diag_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1293_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v_usedTheorems_1250_ = lean_ctor_get(v_a_1249_, 0);
v_diag_1251_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1253_ = v_a_1249_;
v_isShared_1254_ = v_isSharedCheck_1293_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_diag_1251_);
lean_inc(v_usedTheorems_1250_);
lean_dec(v_a_1249_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1293_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1236_, v_usedTheorems_1250_, v___y_1242_, v___y_1239_, v___y_1237_, v___y_1240_);
lean_dec_ref(v_usedTheorems_1250_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_ref_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_ref_1257_ = lean_ctor_get(v___y_1237_, 2);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v_a_1256_);
lean_ctor_set(v___x_1253_, 0, v___x_1258_);
v___x_1260_ = v___x_1253_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1256_);
v___x_1260_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
lean_ctor_set(v___x_1262_, 4, v___x_1261_);
lean_ctor_set(v___x_1262_, 5, v___x_1261_);
lean_inc(v_ref_1257_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_ref_1257_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1265_ = 4;
v___x_1266_ = l_Lean_MessageData_nil;
v___x_1267_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1231_, v___x_1262_, v___x_1263_, v___x_1264_, v___x_1261_, v___x_1265_, v___x_1266_, v___y_1237_, v___y_1240_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_diag_1251_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_diag_1251_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_diag_1251_);
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1253_);
lean_dec_ref(v_diag_1251_);
lean_dec(v_tk_1231_);
v_a_1285_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1255_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1255_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___y_1236_);
lean_dec(v_tk_1231_);
v_a_1294_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1248_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1248_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v___jp_1302_:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = 0;
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1318_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1306_, v___x_1316_, v___y_1304_, v___x_1316_, v___x_1317_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1306_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
if (lean_obj_tag(v___y_1305_) == 0)
{
lean_object* v_ctx_1320_; lean_object* v_simprocs_1321_; lean_object* v_dischargeWrapper_1322_; 
v_ctx_1320_ = lean_ctor_get(v_a_1319_, 0);
lean_inc_ref(v_ctx_1320_);
v_simprocs_1321_ = lean_ctor_get(v_a_1319_, 1);
lean_inc_ref(v_simprocs_1321_);
v_dischargeWrapper_1322_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_dischargeWrapper_1322_);
lean_dec(v_a_1319_);
v___y_1233_ = v_dischargeWrapper_1322_;
v___y_1234_ = v___y_1303_;
v___y_1235_ = v_simprocs_1321_;
v___y_1236_ = v_stxForSuggestion_1307_;
v___y_1237_ = v___y_1314_;
v___y_1238_ = v___y_1310_;
v___y_1239_ = v___y_1313_;
v___y_1240_ = v___y_1315_;
v___y_1241_ = v___y_1308_;
v___y_1242_ = v___y_1312_;
v___y_1243_ = v___y_1311_;
v___y_1244_ = v___y_1309_;
v___y_1245_ = v_ctx_1320_;
goto v___jp_1232_;
}
else
{
lean_object* v_ctx_1323_; lean_object* v_simprocs_1324_; lean_object* v_dischargeWrapper_1325_; lean_object* v___x_1326_; 
lean_dec_ref_known(v___y_1305_, 1);
v_ctx_1323_ = lean_ctor_get(v_a_1319_, 0);
lean_inc_ref(v_ctx_1323_);
v_simprocs_1324_ = lean_ctor_get(v_a_1319_, 1);
lean_inc_ref(v_simprocs_1324_);
v_dischargeWrapper_1325_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_dischargeWrapper_1325_);
lean_dec(v_a_1319_);
v___x_1326_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1323_);
v___y_1233_ = v_dischargeWrapper_1325_;
v___y_1234_ = v___y_1303_;
v___y_1235_ = v_simprocs_1324_;
v___y_1236_ = v_stxForSuggestion_1307_;
v___y_1237_ = v___y_1314_;
v___y_1238_ = v___y_1310_;
v___y_1239_ = v___y_1313_;
v___y_1240_ = v___y_1315_;
v___y_1241_ = v___y_1308_;
v___y_1242_ = v___y_1312_;
v___y_1243_ = v___y_1311_;
v___y_1244_ = v___y_1309_;
v___y_1245_ = v___x_1326_;
goto v___jp_1232_;
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_stxForSuggestion_1307_);
lean_dec(v___y_1305_);
lean_dec(v___y_1303_);
lean_dec(v_tk_1231_);
v_a_1327_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1318_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1318_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1335_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v___y_1350_);
v___x_1358_ = l_Array_append___redArg(v___y_1350_, v___y_1357_);
lean_dec_ref(v___y_1357_);
lean_inc(v___y_1347_);
lean_inc(v___y_1348_);
v___x_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1348_);
lean_ctor_set(v___x_1359_, 1, v___y_1347_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_node6(v___y_1348_, v___y_1344_, v___y_1341_, v___y_1337_, v___y_1342_, v___y_1343_, v___y_1355_, v___x_1359_);
v___y_1303_ = v___y_1336_;
v___y_1304_ = v___y_1338_;
v___y_1305_ = v___y_1345_;
v___y_1306_ = v___y_1353_;
v_stxForSuggestion_1307_ = v___x_1360_;
v___y_1308_ = v___y_1340_;
v___y_1309_ = v___y_1356_;
v___y_1310_ = v___y_1339_;
v___y_1311_ = v___y_1349_;
v___y_1312_ = v___y_1354_;
v___y_1313_ = v___y_1351_;
v___y_1314_ = v___y_1352_;
v___y_1315_ = v___y_1346_;
goto v___jp_1302_;
}
v___jp_1361_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_inc_ref_n(v___y_1376_, 2);
v___x_1384_ = l_Array_append___redArg(v___y_1376_, v___y_1383_);
lean_dec_ref(v___y_1383_);
lean_inc_n(v___y_1373_, 3);
lean_inc_n(v___y_1374_, 5);
v___x_1385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1374_);
lean_ctor_set(v___x_1385_, 1, v___y_1373_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1374_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1389_ = l_Lean_Syntax_SepArray_ofElems(v___x_1388_, v___y_1371_);
lean_dec_ref(v___y_1371_);
v___x_1390_ = l_Array_append___redArg(v___y_1376_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1374_);
lean_ctor_set(v___x_1391_, 1, v___y_1373_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1374_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_node3(v___y_1374_, v___y_1373_, v___x_1387_, v___x_1391_, v___x_1393_);
if (lean_obj_tag(v___y_1381_) == 1)
{
lean_object* v_val_1395_; lean_object* v___x_1396_; 
v_val_1395_ = lean_ctor_get(v___y_1381_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___y_1381_, 1);
v___x_1396_ = l_Array_mkArray1___redArg(v_val_1395_);
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1365_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1368_;
v___y_1343_ = v___x_1385_;
v___y_1344_ = v___y_1369_;
v___y_1345_ = v___y_1370_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1374_;
v___y_1349_ = v___y_1375_;
v___y_1350_ = v___y_1376_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v___y_1378_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___x_1394_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___x_1396_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1397_; 
lean_dec(v___y_1381_);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1365_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1368_;
v___y_1343_ = v___x_1385_;
v___y_1344_ = v___y_1369_;
v___y_1345_ = v___y_1370_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1374_;
v___y_1349_ = v___y_1375_;
v___y_1350_ = v___y_1376_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v___y_1378_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___x_1394_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___x_1397_;
goto v___jp_1335_;
}
}
v___jp_1398_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_inc_ref(v___y_1413_);
v___x_1421_ = l_Array_append___redArg(v___y_1413_, v___y_1420_);
lean_dec_ref(v___y_1420_);
lean_inc(v___y_1410_);
lean_inc(v___y_1411_);
v___x_1422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1411_);
lean_ctor_set(v___x_1422_, 1, v___y_1410_);
lean_ctor_set(v___x_1422_, 2, v___x_1421_);
if (lean_obj_tag(v___y_1404_) == 1)
{
lean_object* v_val_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_val_1423_ = lean_ctor_get(v___y_1404_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___y_1404_, 1);
v___x_1424_ = l_Lean_SourceInfo_fromRef(v_val_1423_, v___x_1215_);
lean_dec(v_val_1423_);
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Array_mkArray1___redArg(v___x_1426_);
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1403_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___x_1422_;
v___y_1369_ = v___y_1406_;
v___y_1370_ = v___y_1407_;
v___y_1371_ = v___y_1408_;
v___y_1372_ = v___y_1409_;
v___y_1373_ = v___y_1410_;
v___y_1374_ = v___y_1411_;
v___y_1375_ = v___y_1412_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___y_1414_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1417_;
v___y_1381_ = v___y_1418_;
v___y_1382_ = v___y_1419_;
v___y_1383_ = v___x_1427_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1428_; 
lean_dec(v___y_1404_);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1403_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___x_1422_;
v___y_1369_ = v___y_1406_;
v___y_1370_ = v___y_1407_;
v___y_1371_ = v___y_1408_;
v___y_1372_ = v___y_1409_;
v___y_1373_ = v___y_1410_;
v___y_1374_ = v___y_1411_;
v___y_1375_ = v___y_1412_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___y_1414_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1417_;
v___y_1381_ = v___y_1418_;
v___y_1382_ = v___y_1419_;
v___y_1383_ = v___x_1428_;
goto v___jp_1361_;
}
}
v___jp_1429_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_inc_ref(v___y_1438_);
v___x_1452_ = l_Array_append___redArg(v___y_1438_, v___y_1451_);
lean_dec_ref(v___y_1451_);
lean_inc(v___y_1443_);
lean_inc(v___y_1446_);
v___x_1453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1446_);
lean_ctor_set(v___x_1453_, 1, v___y_1443_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
v___x_1454_ = l_Lean_Syntax_node6(v___y_1446_, v___y_1436_, v___y_1449_, v___y_1432_, v___y_1431_, v___y_1440_, v___y_1450_, v___x_1453_);
v___y_1303_ = v___y_1430_;
v___y_1304_ = v___y_1433_;
v___y_1305_ = v___y_1437_;
v___y_1306_ = v___y_1445_;
v_stxForSuggestion_1307_ = v___x_1454_;
v___y_1308_ = v___y_1435_;
v___y_1309_ = v___y_1448_;
v___y_1310_ = v___y_1434_;
v___y_1311_ = v___y_1441_;
v___y_1312_ = v___y_1447_;
v___y_1313_ = v___y_1442_;
v___y_1314_ = v___y_1444_;
v___y_1315_ = v___y_1439_;
goto v___jp_1302_;
}
v___jp_1455_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_inc_ref_n(v___y_1464_, 2);
v___x_1478_ = l_Array_append___redArg(v___y_1464_, v___y_1477_);
lean_dec_ref(v___y_1477_);
lean_inc_n(v___y_1469_, 3);
lean_inc_n(v___y_1472_, 5);
v___x_1479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1479_, 0, v___y_1472_);
lean_ctor_set(v___x_1479_, 1, v___y_1469_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1472_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1483_ = l_Lean_Syntax_SepArray_ofElems(v___x_1482_, v___y_1465_);
lean_dec_ref(v___y_1465_);
v___x_1484_ = l_Array_append___redArg(v___y_1464_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1472_);
lean_ctor_set(v___x_1485_, 1, v___y_1469_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
v___x_1486_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1472_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node3(v___y_1472_, v___y_1469_, v___x_1481_, v___x_1485_, v___x_1487_);
if (lean_obj_tag(v___y_1474_) == 1)
{
lean_object* v_val_1489_; lean_object* v___x_1490_; 
v_val_1489_ = lean_ctor_get(v___y_1474_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v___y_1474_, 1);
v___x_1490_ = l_Array_mkArray1___redArg(v_val_1489_);
v___y_1430_ = v___y_1456_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___y_1459_;
v___y_1434_ = v___y_1460_;
v___y_1435_ = v___y_1461_;
v___y_1436_ = v___y_1462_;
v___y_1437_ = v___y_1463_;
v___y_1438_ = v___y_1464_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___x_1479_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v___y_1469_;
v___y_1444_ = v___y_1470_;
v___y_1445_ = v___y_1471_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___y_1473_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___x_1488_;
v___y_1451_ = v___x_1490_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v___y_1474_);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1430_ = v___y_1456_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___y_1459_;
v___y_1434_ = v___y_1460_;
v___y_1435_ = v___y_1461_;
v___y_1436_ = v___y_1462_;
v___y_1437_ = v___y_1463_;
v___y_1438_ = v___y_1464_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___x_1479_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v___y_1469_;
v___y_1444_ = v___y_1470_;
v___y_1445_ = v___y_1471_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___y_1473_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___x_1488_;
v___y_1451_ = v___x_1491_;
goto v___jp_1429_;
}
}
v___jp_1492_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v___y_1501_);
v___x_1515_ = l_Array_append___redArg(v___y_1501_, v___y_1514_);
lean_dec_ref(v___y_1514_);
lean_inc(v___y_1506_);
lean_inc(v___y_1509_);
v___x_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1509_);
lean_ctor_set(v___x_1516_, 1, v___y_1506_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
if (lean_obj_tag(v___y_1498_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_val_1517_ = lean_ctor_get(v___y_1498_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___y_1498_, 1);
v___x_1518_ = l_Lean_SourceInfo_fromRef(v_val_1517_, v___x_1215_);
lean_dec(v_val_1517_);
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Array_mkArray1___redArg(v___x_1520_);
v___y_1456_ = v___y_1493_;
v___y_1457_ = v___x_1516_;
v___y_1458_ = v___y_1494_;
v___y_1459_ = v___y_1495_;
v___y_1460_ = v___y_1496_;
v___y_1461_ = v___y_1497_;
v___y_1462_ = v___y_1499_;
v___y_1463_ = v___y_1500_;
v___y_1464_ = v___y_1501_;
v___y_1465_ = v___y_1502_;
v___y_1466_ = v___y_1503_;
v___y_1467_ = v___y_1504_;
v___y_1468_ = v___y_1505_;
v___y_1469_ = v___y_1506_;
v___y_1470_ = v___y_1507_;
v___y_1471_ = v___y_1508_;
v___y_1472_ = v___y_1509_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___y_1511_;
v___y_1475_ = v___y_1512_;
v___y_1476_ = v___y_1513_;
v___y_1477_ = v___x_1521_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v___y_1498_);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1456_ = v___y_1493_;
v___y_1457_ = v___x_1516_;
v___y_1458_ = v___y_1494_;
v___y_1459_ = v___y_1495_;
v___y_1460_ = v___y_1496_;
v___y_1461_ = v___y_1497_;
v___y_1462_ = v___y_1499_;
v___y_1463_ = v___y_1500_;
v___y_1464_ = v___y_1501_;
v___y_1465_ = v___y_1502_;
v___y_1466_ = v___y_1503_;
v___y_1467_ = v___y_1504_;
v___y_1468_ = v___y_1505_;
v___y_1469_ = v___y_1506_;
v___y_1470_ = v___y_1507_;
v___y_1471_ = v___y_1508_;
v___y_1472_ = v___y_1509_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___y_1511_;
v___y_1475_ = v___y_1512_;
v___y_1476_ = v___y_1513_;
v___y_1477_ = v___x_1522_;
goto v___jp_1455_;
}
}
v___jp_1523_:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1531_);
if (lean_obj_tag(v___y_1527_) == 0)
{
lean_object* v_a_1542_; lean_object* v_ref_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v_ref_1543_ = lean_ctor_get(v___y_1539_, 2);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_ref_1543_, v___x_1544_);
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1547_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1546_);
v___x_1548_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1546_);
v___x_1550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1551_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1530_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1553_; 
v_val_1552_ = lean_ctor_get(v___y_1530_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___y_1530_, 1);
v___x_1553_ = l_Array_mkArray1___redArg(v_val_1552_);
v___y_1493_ = v___y_1524_;
v___y_1494_ = v_a_1542_;
v___y_1495_ = v___y_1525_;
v___y_1496_ = v___y_1535_;
v___y_1497_ = v___y_1533_;
v___y_1498_ = v___y_1526_;
v___y_1499_ = v___x_1547_;
v___y_1500_ = v___y_1527_;
v___y_1501_ = v___x_1551_;
v___y_1502_ = v___y_1528_;
v___y_1503_ = v___y_1540_;
v___y_1504_ = v___y_1536_;
v___y_1505_ = v___y_1538_;
v___y_1506_ = v___x_1550_;
v___y_1507_ = v___y_1539_;
v___y_1508_ = v_stxForExecution_1532_;
v___y_1509_ = v___x_1545_;
v___y_1510_ = v___y_1537_;
v___y_1511_ = v___y_1529_;
v___y_1512_ = v___y_1534_;
v___y_1513_ = v___x_1549_;
v___y_1514_ = v___x_1553_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1554_; 
lean_dec(v___y_1530_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1493_ = v___y_1524_;
v___y_1494_ = v_a_1542_;
v___y_1495_ = v___y_1525_;
v___y_1496_ = v___y_1535_;
v___y_1497_ = v___y_1533_;
v___y_1498_ = v___y_1526_;
v___y_1499_ = v___x_1547_;
v___y_1500_ = v___y_1527_;
v___y_1501_ = v___x_1551_;
v___y_1502_ = v___y_1528_;
v___y_1503_ = v___y_1540_;
v___y_1504_ = v___y_1536_;
v___y_1505_ = v___y_1538_;
v___y_1506_ = v___x_1550_;
v___y_1507_ = v___y_1539_;
v___y_1508_ = v_stxForExecution_1532_;
v___y_1509_ = v___x_1545_;
v___y_1510_ = v___y_1537_;
v___y_1511_ = v___y_1529_;
v___y_1512_ = v___y_1534_;
v___y_1513_ = v___x_1549_;
v___y_1514_ = v___x_1554_;
goto v___jp_1492_;
}
}
else
{
lean_object* v_a_1555_; lean_object* v_ref_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1555_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1541_);
v_ref_1556_ = lean_ctor_get(v___y_1539_, 2);
v___x_1557_ = 0;
v___x_1558_ = l_Lean_SourceInfo_fromRef(v_ref_1556_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1560_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1559_);
v___x_1561_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1565_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1530_) == 1)
{
lean_object* v_val_1566_; lean_object* v___x_1567_; 
v_val_1566_ = lean_ctor_get(v___y_1530_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___y_1530_, 1);
v___x_1567_ = l_Array_mkArray1___redArg(v_val_1566_);
v___y_1399_ = v___y_1524_;
v___y_1400_ = v_a_1555_;
v___y_1401_ = v___y_1525_;
v___y_1402_ = v___y_1535_;
v___y_1403_ = v___y_1533_;
v___y_1404_ = v___y_1526_;
v___y_1405_ = v___x_1563_;
v___y_1406_ = v___x_1560_;
v___y_1407_ = v___y_1527_;
v___y_1408_ = v___y_1528_;
v___y_1409_ = v___y_1540_;
v___y_1410_ = v___x_1564_;
v___y_1411_ = v___x_1558_;
v___y_1412_ = v___y_1536_;
v___y_1413_ = v___x_1565_;
v___y_1414_ = v___y_1538_;
v___y_1415_ = v___y_1539_;
v___y_1416_ = v_stxForExecution_1532_;
v___y_1417_ = v___y_1537_;
v___y_1418_ = v___y_1529_;
v___y_1419_ = v___y_1534_;
v___y_1420_ = v___x_1567_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1568_; 
lean_dec(v___y_1530_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1399_ = v___y_1524_;
v___y_1400_ = v_a_1555_;
v___y_1401_ = v___y_1525_;
v___y_1402_ = v___y_1535_;
v___y_1403_ = v___y_1533_;
v___y_1404_ = v___y_1526_;
v___y_1405_ = v___x_1563_;
v___y_1406_ = v___x_1560_;
v___y_1407_ = v___y_1527_;
v___y_1408_ = v___y_1528_;
v___y_1409_ = v___y_1540_;
v___y_1410_ = v___x_1564_;
v___y_1411_ = v___x_1558_;
v___y_1412_ = v___y_1536_;
v___y_1413_ = v___x_1565_;
v___y_1414_ = v___y_1538_;
v___y_1415_ = v___y_1539_;
v___y_1416_ = v_stxForExecution_1532_;
v___y_1417_ = v___y_1537_;
v___y_1418_ = v___y_1529_;
v___y_1419_ = v___y_1534_;
v___y_1420_ = v___x_1568_;
goto v___jp_1398_;
}
}
}
v___jp_1569_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_inc_ref(v___y_1585_);
v___x_1595_ = l_Array_append___redArg(v___y_1585_, v___y_1594_);
lean_dec_ref(v___y_1594_);
lean_inc(v___y_1581_);
lean_inc(v___y_1586_);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1586_);
lean_ctor_set(v___x_1596_, 1, v___y_1581_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
lean_inc(v___y_1583_);
v___x_1597_ = l_Lean_Syntax_node6(v___y_1586_, v___y_1571_, v___y_1573_, v___y_1583_, v___y_1575_, v___y_1590_, v___y_1591_, v___x_1596_);
v___y_1524_ = v___y_1570_;
v___y_1525_ = v___y_1572_;
v___y_1526_ = v___y_1576_;
v___y_1527_ = v___y_1578_;
v___y_1528_ = v___y_1579_;
v___y_1529_ = v___y_1588_;
v___y_1530_ = v___y_1593_;
v___y_1531_ = v___y_1583_;
v_stxForExecution_1532_ = v___x_1597_;
v___y_1533_ = v___y_1580_;
v___y_1534_ = v___y_1584_;
v___y_1535_ = v___y_1592_;
v___y_1536_ = v___y_1582_;
v___y_1537_ = v___y_1587_;
v___y_1538_ = v___y_1577_;
v___y_1539_ = v___y_1589_;
v___y_1540_ = v___y_1574_;
goto v___jp_1523_;
}
v___jp_1598_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_inc_ref_n(v___y_1614_, 2);
v___x_1622_ = l_Array_append___redArg(v___y_1614_, v___y_1621_);
lean_dec_ref(v___y_1621_);
lean_inc_n(v___y_1611_, 3);
lean_inc_n(v___y_1615_, 5);
v___x_1623_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1623_, 0, v___y_1615_);
lean_ctor_set(v___x_1623_, 1, v___y_1611_);
lean_ctor_set(v___x_1623_, 2, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1615_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1627_ = l_Lean_Syntax_SepArray_ofElems(v___x_1626_, v___y_1608_);
v___x_1628_ = l_Array_append___redArg(v___y_1614_, v___x_1627_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1615_);
lean_ctor_set(v___x_1629_, 1, v___y_1611_);
lean_ctor_set(v___x_1629_, 2, v___x_1628_);
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___y_1615_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_Syntax_node3(v___y_1615_, v___y_1611_, v___x_1625_, v___x_1629_, v___x_1631_);
if (lean_obj_tag(v___y_1617_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1634_; 
v_val_1633_ = lean_ctor_get(v___y_1617_, 0);
lean_inc(v_val_1633_);
v___x_1634_ = l_Array_mkArray1___redArg(v_val_1633_);
v___y_1570_ = v___y_1599_;
v___y_1571_ = v___y_1600_;
v___y_1572_ = v___y_1601_;
v___y_1573_ = v___y_1602_;
v___y_1574_ = v___y_1603_;
v___y_1575_ = v___y_1604_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1606_;
v___y_1578_ = v___y_1607_;
v___y_1579_ = v___y_1608_;
v___y_1580_ = v___y_1609_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1610_;
v___y_1583_ = v___y_1612_;
v___y_1584_ = v___y_1613_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___y_1615_;
v___y_1587_ = v___y_1616_;
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1618_;
v___y_1590_ = v___x_1623_;
v___y_1591_ = v___x_1632_;
v___y_1592_ = v___y_1619_;
v___y_1593_ = v___y_1620_;
v___y_1594_ = v___x_1634_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1570_ = v___y_1599_;
v___y_1571_ = v___y_1600_;
v___y_1572_ = v___y_1601_;
v___y_1573_ = v___y_1602_;
v___y_1574_ = v___y_1603_;
v___y_1575_ = v___y_1604_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1606_;
v___y_1578_ = v___y_1607_;
v___y_1579_ = v___y_1608_;
v___y_1580_ = v___y_1609_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1610_;
v___y_1583_ = v___y_1612_;
v___y_1584_ = v___y_1613_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___y_1615_;
v___y_1587_ = v___y_1616_;
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1618_;
v___y_1590_ = v___x_1623_;
v___y_1591_ = v___x_1632_;
v___y_1592_ = v___y_1619_;
v___y_1593_ = v___y_1620_;
v___y_1594_ = v___x_1635_;
goto v___jp_1569_;
}
}
v___jp_1636_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_inc_ref(v___y_1651_);
v___x_1659_ = l_Array_append___redArg(v___y_1651_, v___y_1658_);
lean_dec_ref(v___y_1658_);
lean_inc(v___y_1647_);
lean_inc(v___y_1652_);
v___x_1660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1652_);
lean_ctor_set(v___x_1660_, 1, v___y_1647_);
lean_ctor_set(v___x_1660_, 2, v___x_1659_);
if (lean_obj_tag(v___y_1642_) == 1)
{
lean_object* v_val_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_val_1661_ = lean_ctor_get(v___y_1642_, 0);
v___x_1662_ = l_Lean_SourceInfo_fromRef(v_val_1661_, v___x_1215_);
v___x_1663_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Array_mkArray1___redArg(v___x_1664_);
v___y_1599_ = v___y_1637_;
v___y_1600_ = v___y_1638_;
v___y_1601_ = v___y_1639_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1641_;
v___y_1604_ = v___x_1660_;
v___y_1605_ = v___y_1642_;
v___y_1606_ = v___y_1643_;
v___y_1607_ = v___y_1644_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___y_1646_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1647_;
v___y_1612_ = v___y_1649_;
v___y_1613_ = v___y_1650_;
v___y_1614_ = v___y_1651_;
v___y_1615_ = v___y_1652_;
v___y_1616_ = v___y_1653_;
v___y_1617_ = v___y_1654_;
v___y_1618_ = v___y_1655_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___x_1665_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1599_ = v___y_1637_;
v___y_1600_ = v___y_1638_;
v___y_1601_ = v___y_1639_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1641_;
v___y_1604_ = v___x_1660_;
v___y_1605_ = v___y_1642_;
v___y_1606_ = v___y_1643_;
v___y_1607_ = v___y_1644_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___y_1646_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1647_;
v___y_1612_ = v___y_1649_;
v___y_1613_ = v___y_1650_;
v___y_1614_ = v___y_1651_;
v___y_1615_ = v___y_1652_;
v___y_1616_ = v___y_1653_;
v___y_1617_ = v___y_1654_;
v___y_1618_ = v___y_1655_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___x_1666_;
goto v___jp_1598_;
}
}
v___jp_1667_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v___y_1691_);
v___x_1693_ = l_Array_append___redArg(v___y_1691_, v___y_1692_);
lean_dec_ref(v___y_1692_);
lean_inc(v___y_1688_);
lean_inc(v___y_1687_);
v___x_1694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1694_, 0, v___y_1687_);
lean_ctor_set(v___x_1694_, 1, v___y_1688_);
lean_ctor_set(v___x_1694_, 2, v___x_1693_);
lean_inc(v___y_1681_);
v___x_1695_ = l_Lean_Syntax_node6(v___y_1687_, v___y_1671_, v___y_1678_, v___y_1681_, v___y_1675_, v___y_1677_, v___y_1684_, v___x_1694_);
v___y_1524_ = v___y_1668_;
v___y_1525_ = v___y_1669_;
v___y_1526_ = v___y_1672_;
v___y_1527_ = v___y_1674_;
v___y_1528_ = v___y_1676_;
v___y_1529_ = v___y_1685_;
v___y_1530_ = v___y_1690_;
v___y_1531_ = v___y_1681_;
v_stxForExecution_1532_ = v___x_1695_;
v___y_1533_ = v___y_1679_;
v___y_1534_ = v___y_1682_;
v___y_1535_ = v___y_1689_;
v___y_1536_ = v___y_1680_;
v___y_1537_ = v___y_1683_;
v___y_1538_ = v___y_1673_;
v___y_1539_ = v___y_1686_;
v___y_1540_ = v___y_1670_;
goto v___jp_1523_;
}
v___jp_1696_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_inc_ref_n(v___y_1718_, 2);
v___x_1720_ = l_Array_append___redArg(v___y_1718_, v___y_1719_);
lean_dec_ref(v___y_1719_);
lean_inc_n(v___y_1715_, 3);
lean_inc_n(v___y_1714_, 5);
v___x_1721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1714_);
lean_ctor_set(v___x_1721_, 1, v___y_1715_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___y_1714_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1725_ = l_Lean_Syntax_SepArray_ofElems(v___x_1724_, v___y_1705_);
v___x_1726_ = l_Array_append___redArg(v___y_1718_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1727_, 0, v___y_1714_);
lean_ctor_set(v___x_1727_, 1, v___y_1715_);
lean_ctor_set(v___x_1727_, 2, v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___y_1714_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_Syntax_node3(v___y_1714_, v___y_1715_, v___x_1723_, v___x_1727_, v___x_1729_);
if (lean_obj_tag(v___y_1712_) == 1)
{
lean_object* v_val_1731_; lean_object* v___x_1732_; 
v_val_1731_ = lean_ctor_get(v___y_1712_, 0);
lean_inc(v_val_1731_);
v___x_1732_ = l_Array_mkArray1___redArg(v_val_1731_);
v___y_1668_ = v___y_1697_;
v___y_1669_ = v___y_1698_;
v___y_1670_ = v___y_1699_;
v___y_1671_ = v___y_1700_;
v___y_1672_ = v___y_1701_;
v___y_1673_ = v___y_1702_;
v___y_1674_ = v___y_1703_;
v___y_1675_ = v___y_1704_;
v___y_1676_ = v___y_1705_;
v___y_1677_ = v___x_1721_;
v___y_1678_ = v___y_1706_;
v___y_1679_ = v___y_1707_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1710_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___x_1730_;
v___y_1685_ = v___y_1712_;
v___y_1686_ = v___y_1713_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v___y_1715_;
v___y_1689_ = v___y_1716_;
v___y_1690_ = v___y_1717_;
v___y_1691_ = v___y_1718_;
v___y_1692_ = v___x_1732_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1668_ = v___y_1697_;
v___y_1669_ = v___y_1698_;
v___y_1670_ = v___y_1699_;
v___y_1671_ = v___y_1700_;
v___y_1672_ = v___y_1701_;
v___y_1673_ = v___y_1702_;
v___y_1674_ = v___y_1703_;
v___y_1675_ = v___y_1704_;
v___y_1676_ = v___y_1705_;
v___y_1677_ = v___x_1721_;
v___y_1678_ = v___y_1706_;
v___y_1679_ = v___y_1707_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1710_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___x_1730_;
v___y_1685_ = v___y_1712_;
v___y_1686_ = v___y_1713_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v___y_1715_;
v___y_1689_ = v___y_1716_;
v___y_1690_ = v___y_1717_;
v___y_1691_ = v___y_1718_;
v___y_1692_ = v___x_1733_;
goto v___jp_1667_;
}
}
v___jp_1734_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_inc_ref(v___y_1755_);
v___x_1757_ = l_Array_append___redArg(v___y_1755_, v___y_1756_);
lean_dec_ref(v___y_1756_);
lean_inc(v___y_1752_);
lean_inc(v___y_1751_);
v___x_1758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1751_);
lean_ctor_set(v___x_1758_, 1, v___y_1752_);
lean_ctor_set(v___x_1758_, 2, v___x_1757_);
if (lean_obj_tag(v___y_1739_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_val_1759_ = lean_ctor_get(v___y_1739_, 0);
v___x_1760_ = l_Lean_SourceInfo_fromRef(v_val_1759_, v___x_1215_);
v___x_1761_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Array_mkArray1___redArg(v___x_1762_);
v___y_1697_ = v___y_1735_;
v___y_1698_ = v___y_1736_;
v___y_1699_ = v___y_1737_;
v___y_1700_ = v___y_1738_;
v___y_1701_ = v___y_1739_;
v___y_1702_ = v___y_1740_;
v___y_1703_ = v___y_1741_;
v___y_1704_ = v___x_1758_;
v___y_1705_ = v___y_1742_;
v___y_1706_ = v___y_1743_;
v___y_1707_ = v___y_1744_;
v___y_1708_ = v___y_1745_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1748_;
v___y_1712_ = v___y_1749_;
v___y_1713_ = v___y_1750_;
v___y_1714_ = v___y_1751_;
v___y_1715_ = v___y_1752_;
v___y_1716_ = v___y_1753_;
v___y_1717_ = v___y_1754_;
v___y_1718_ = v___y_1755_;
v___y_1719_ = v___x_1763_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1697_ = v___y_1735_;
v___y_1698_ = v___y_1736_;
v___y_1699_ = v___y_1737_;
v___y_1700_ = v___y_1738_;
v___y_1701_ = v___y_1739_;
v___y_1702_ = v___y_1740_;
v___y_1703_ = v___y_1741_;
v___y_1704_ = v___x_1758_;
v___y_1705_ = v___y_1742_;
v___y_1706_ = v___y_1743_;
v___y_1707_ = v___y_1744_;
v___y_1708_ = v___y_1745_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1748_;
v___y_1712_ = v___y_1749_;
v___y_1713_ = v___y_1750_;
v___y_1714_ = v___y_1751_;
v___y_1715_ = v___y_1752_;
v___y_1716_ = v___y_1753_;
v___y_1717_ = v___y_1754_;
v___y_1718_ = v___y_1755_;
v___y_1719_ = v___x_1764_;
goto v___jp_1696_;
}
}
v___jp_1765_:
{
if (lean_obj_tag(v___y_1769_) == 0)
{
lean_object* v_ref_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_ref_1782_ = lean_ctor_get(v___y_1780_, 2);
v___x_1783_ = 0;
v___x_1784_ = l_Lean_SourceInfo_fromRef(v_ref_1782_, v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_1786_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1785_);
v___x_1787_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v___x_1785_);
v___x_1789_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1790_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1772_) == 1)
{
lean_object* v_val_1791_; lean_object* v___x_1792_; 
v_val_1791_ = lean_ctor_get(v___y_1772_, 0);
lean_inc(v_val_1791_);
v___x_1792_ = l_Array_mkArray1___redArg(v_val_1791_);
v___y_1735_ = v___y_1766_;
v___y_1736_ = v___y_1767_;
v___y_1737_ = v___y_1781_;
v___y_1738_ = v___x_1786_;
v___y_1739_ = v___y_1768_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1769_;
v___y_1742_ = v_argsArray_1773_;
v___y_1743_ = v___x_1788_;
v___y_1744_ = v___y_1774_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1775_;
v___y_1748_ = v___y_1778_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___y_1780_;
v___y_1751_ = v___x_1784_;
v___y_1752_ = v___x_1789_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1772_;
v___y_1755_ = v___x_1790_;
v___y_1756_ = v___x_1792_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1735_ = v___y_1766_;
v___y_1736_ = v___y_1767_;
v___y_1737_ = v___y_1781_;
v___y_1738_ = v___x_1786_;
v___y_1739_ = v___y_1768_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1769_;
v___y_1742_ = v_argsArray_1773_;
v___y_1743_ = v___x_1788_;
v___y_1744_ = v___y_1774_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1775_;
v___y_1748_ = v___y_1778_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___y_1780_;
v___y_1751_ = v___x_1784_;
v___y_1752_ = v___x_1789_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1772_;
v___y_1755_ = v___x_1790_;
v___y_1756_ = v___x_1793_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_ref_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_ref_1794_ = lean_ctor_get(v___y_1780_, 2);
v___x_1795_ = 0;
v___x_1796_ = l_Lean_SourceInfo_fromRef(v_ref_1794_, v___x_1795_);
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_1798_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1797_);
v___x_1799_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1803_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1772_) == 1)
{
lean_object* v_val_1804_; lean_object* v___x_1805_; 
v_val_1804_ = lean_ctor_get(v___y_1772_, 0);
lean_inc(v_val_1804_);
v___x_1805_ = l_Array_mkArray1___redArg(v_val_1804_);
v___y_1637_ = v___y_1766_;
v___y_1638_ = v___x_1798_;
v___y_1639_ = v___y_1767_;
v___y_1640_ = v___x_1801_;
v___y_1641_ = v___y_1781_;
v___y_1642_ = v___y_1768_;
v___y_1643_ = v___y_1779_;
v___y_1644_ = v___y_1769_;
v___y_1645_ = v_argsArray_1773_;
v___y_1646_ = v___y_1774_;
v___y_1647_ = v___x_1802_;
v___y_1648_ = v___y_1777_;
v___y_1649_ = v___y_1771_;
v___y_1650_ = v___y_1775_;
v___y_1651_ = v___x_1803_;
v___y_1652_ = v___x_1796_;
v___y_1653_ = v___y_1778_;
v___y_1654_ = v___y_1770_;
v___y_1655_ = v___y_1780_;
v___y_1656_ = v___y_1776_;
v___y_1657_ = v___y_1772_;
v___y_1658_ = v___x_1805_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1637_ = v___y_1766_;
v___y_1638_ = v___x_1798_;
v___y_1639_ = v___y_1767_;
v___y_1640_ = v___x_1801_;
v___y_1641_ = v___y_1781_;
v___y_1642_ = v___y_1768_;
v___y_1643_ = v___y_1779_;
v___y_1644_ = v___y_1769_;
v___y_1645_ = v_argsArray_1773_;
v___y_1646_ = v___y_1774_;
v___y_1647_ = v___x_1802_;
v___y_1648_ = v___y_1777_;
v___y_1649_ = v___y_1771_;
v___y_1650_ = v___y_1775_;
v___y_1651_ = v___x_1803_;
v___y_1652_ = v___x_1796_;
v___y_1653_ = v___y_1778_;
v___y_1654_ = v___y_1770_;
v___y_1655_ = v___y_1780_;
v___y_1656_ = v___y_1776_;
v___y_1657_ = v___y_1772_;
v___y_1658_ = v___x_1806_;
goto v___jp_1636_;
}
}
}
v___jp_1807_:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1810_, v___y_1817_, v___y_1822_, v___y_1813_, v___y_1821_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l_Lean_LibrarySuggestions_select(v_a_1826_, v___y_1824_, v___y_1817_, v___y_1822_, v___y_1813_, v___y_1821_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; size_t v_sz_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v_sz_1829_ = lean_array_size(v_a_1828_);
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1828_, v_sz_1829_, v___x_1830_, v___y_1815_, v___y_1820_, v___y_1810_, v___y_1811_, v___y_1818_, v___y_1817_, v___y_1822_, v___y_1813_, v___y_1821_);
lean_dec(v_a_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___y_1766_ = v___y_1808_;
v___y_1767_ = v___y_1809_;
v___y_1768_ = v___y_1812_;
v___y_1769_ = v___y_1814_;
v___y_1770_ = v___y_1819_;
v___y_1771_ = v___y_1816_;
v___y_1772_ = v___y_1823_;
v_argsArray_1773_ = v_a_1832_;
v___y_1774_ = v___y_1820_;
v___y_1775_ = v___y_1810_;
v___y_1776_ = v___y_1811_;
v___y_1777_ = v___y_1818_;
v___y_1778_ = v___y_1817_;
v___y_1779_ = v___y_1822_;
v___y_1780_ = v___y_1813_;
v___y_1781_ = v___y_1821_;
goto v___jp_1765_;
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v___y_1823_);
lean_dec(v___y_1819_);
lean_dec(v___y_1816_);
lean_dec(v___y_1814_);
lean_dec(v___y_1812_);
lean_dec(v___y_1808_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1833_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1831_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1831_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v___y_1823_);
lean_dec(v___y_1819_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec(v___y_1812_);
lean_dec(v___y_1808_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1841_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1827_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1827_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1819_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec(v___y_1812_);
lean_dec(v___y_1808_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1849_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1825_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1825_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
v___jp_1857_:
{
lean_object* v_config_1875_; uint8_t v_suggestions_1876_; 
v_config_1875_ = lean_ctor_get(v___y_1866_, 0);
lean_inc_ref(v_config_1875_);
lean_dec_ref(v___y_1866_);
v_suggestions_1876_ = lean_ctor_get_uint8(v_config_1875_, sizeof(void*)*3 + 26);
if (v_suggestions_1876_ == 0)
{
lean_dec_ref(v_config_1875_);
lean_dec_ref(v___f_1219_);
v___y_1766_ = v___y_1858_;
v___y_1767_ = v___y_1859_;
v___y_1768_ = v___y_1862_;
v___y_1769_ = v___y_1864_;
v___y_1770_ = v___y_1869_;
v___y_1771_ = v___y_1865_;
v___y_1772_ = v___y_1873_;
v_argsArray_1773_ = v___y_1874_;
v___y_1774_ = v___y_1870_;
v___y_1775_ = v___y_1860_;
v___y_1776_ = v___y_1861_;
v___y_1777_ = v___y_1868_;
v___y_1778_ = v___y_1867_;
v___y_1779_ = v___y_1872_;
v___y_1780_ = v___y_1863_;
v___y_1781_ = v___y_1871_;
goto v___jp_1765_;
}
else
{
lean_object* v_maxSuggestions_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_maxSuggestions_1877_ = lean_ctor_get(v_config_1875_, 2);
lean_inc(v_maxSuggestions_1877_);
lean_dec_ref(v_config_1875_);
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1879_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1877_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(100u);
v___x_1881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1878_);
lean_ctor_set(v___x_1881_, 2, v___f_1219_);
lean_ctor_set(v___x_1881_, 3, v___x_1879_);
v___y_1808_ = v___y_1858_;
v___y_1809_ = v___y_1859_;
v___y_1810_ = v___y_1860_;
v___y_1811_ = v___y_1861_;
v___y_1812_ = v___y_1862_;
v___y_1813_ = v___y_1863_;
v___y_1814_ = v___y_1864_;
v___y_1815_ = v___y_1874_;
v___y_1816_ = v___y_1865_;
v___y_1817_ = v___y_1867_;
v___y_1818_ = v___y_1868_;
v___y_1819_ = v___y_1869_;
v___y_1820_ = v___y_1870_;
v___y_1821_ = v___y_1871_;
v___y_1822_ = v___y_1872_;
v___y_1823_ = v___y_1873_;
v___y_1824_ = v___x_1881_;
goto v___jp_1807_;
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1883_; 
v_val_1882_ = lean_ctor_get(v_maxSuggestions_1877_, 0);
lean_inc(v_val_1882_);
lean_dec_ref_known(v_maxSuggestions_1877_, 1);
v___x_1883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1883_, 0, v_val_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1878_);
lean_ctor_set(v___x_1883_, 2, v___f_1219_);
lean_ctor_set(v___x_1883_, 3, v___x_1879_);
v___y_1808_ = v___y_1858_;
v___y_1809_ = v___y_1859_;
v___y_1810_ = v___y_1860_;
v___y_1811_ = v___y_1861_;
v___y_1812_ = v___y_1862_;
v___y_1813_ = v___y_1863_;
v___y_1814_ = v___y_1864_;
v___y_1815_ = v___y_1874_;
v___y_1816_ = v___y_1865_;
v___y_1817_ = v___y_1867_;
v___y_1818_ = v___y_1868_;
v___y_1819_ = v___y_1869_;
v___y_1820_ = v___y_1870_;
v___y_1821_ = v___y_1871_;
v___y_1822_ = v___y_1872_;
v___y_1823_ = v___y_1873_;
v___y_1824_ = v___x_1883_;
goto v___jp_1807_;
}
}
}
v___jp_1884_:
{
uint8_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = 0;
lean_inc(v___y_1896_);
v___x_1900_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1896_, v___x_1899_, v___y_1889_, v___y_1892_, v___y_1888_);
if (lean_obj_tag(v___x_1900_) == 0)
{
if (lean_obj_tag(v___y_1885_) == 1)
{
lean_object* v_a_1901_; lean_object* v_val_1902_; lean_object* v___x_1903_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v_val_1902_ = lean_ctor_get(v___y_1885_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v___y_1885_, 1);
v___x_1903_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1902_);
lean_dec(v_val_1902_);
lean_inc(v___y_1886_);
v___y_1858_ = v___y_1886_;
v___y_1859_ = v___x_1899_;
v___y_1860_ = v___y_1893_;
v___y_1861_ = v___y_1897_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1894_;
v___y_1865_ = v___y_1896_;
v___y_1866_ = v_a_1901_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___y_1895_;
v___y_1869_ = v___y_1886_;
v___y_1870_ = v___y_1889_;
v___y_1871_ = v___y_1888_;
v___y_1872_ = v___y_1891_;
v___y_1873_ = v___y_1898_;
v___y_1874_ = v___x_1903_;
goto v___jp_1857_;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
lean_dec(v___y_1885_);
v_a_1904_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1886_);
v___y_1858_ = v___y_1886_;
v___y_1859_ = v___x_1899_;
v___y_1860_ = v___y_1893_;
v___y_1861_ = v___y_1897_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1894_;
v___y_1865_ = v___y_1896_;
v___y_1866_ = v_a_1904_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___y_1895_;
v___y_1869_ = v___y_1886_;
v___y_1870_ = v___y_1889_;
v___y_1871_ = v___y_1888_;
v___y_1872_ = v___y_1891_;
v___y_1873_ = v___y_1898_;
v___y_1874_ = v___x_1905_;
goto v___jp_1857_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v___y_1898_);
lean_dec(v___y_1896_);
lean_dec(v___y_1894_);
lean_dec(v___y_1890_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1906_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1900_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
v___jp_1914_:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Syntax_getOptional_x3f(v___y_1917_);
lean_dec(v___y_1917_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_box(0);
v___y_1885_ = v___y_1922_;
v___y_1886_ = v___y_1928_;
v___y_1887_ = v___y_1923_;
v___y_1888_ = v___y_1926_;
v___y_1889_ = v___y_1925_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1927_;
v___y_1892_ = v___y_1919_;
v___y_1893_ = v___y_1915_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1924_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1916_;
v___y_1898_ = v___x_1930_;
goto v___jp_1884_;
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_val_1931_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1929_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_val_1931_);
lean_dec(v___x_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_val_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v___y_1885_ = v___y_1922_;
v___y_1886_ = v___y_1928_;
v___y_1887_ = v___y_1923_;
v___y_1888_ = v___y_1926_;
v___y_1889_ = v___y_1925_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1927_;
v___y_1892_ = v___y_1919_;
v___y_1893_ = v___y_1915_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1924_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1916_;
v___y_1898_ = v___x_1936_;
goto v___jp_1884_;
}
}
}
}
v___jp_1939_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_unsigned_to_nat(4u);
v___x_1955_ = l_Lean_Syntax_getArg(v___y_1943_, v___x_1954_);
lean_dec(v___y_1943_);
v___x_1956_ = l_Lean_Syntax_getOptional_x3f(v___x_1955_);
lean_dec(v___x_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_box(0);
v___y_1915_ = v___y_1947_;
v___y_1916_ = v___y_1948_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1940_;
v___y_1919_ = v___y_1952_;
v___y_1920_ = v___y_1942_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v_args_1945_;
v___y_1923_ = v___y_1950_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1946_;
v___y_1926_ = v___y_1953_;
v___y_1927_ = v___y_1951_;
v___y_1928_ = v___x_1957_;
goto v___jp_1914_;
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_val_1958_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_val_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
v___y_1915_ = v___y_1947_;
v___y_1916_ = v___y_1948_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1940_;
v___y_1919_ = v___y_1952_;
v___y_1920_ = v___y_1942_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v_args_1945_;
v___y_1923_ = v___y_1950_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1946_;
v___y_1926_ = v___y_1953_;
v___y_1927_ = v___y_1951_;
v___y_1928_ = v___x_1963_;
goto v___jp_1914_;
}
}
}
}
v___jp_1967_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = lean_unsigned_to_nat(3u);
v___x_1982_ = l_Lean_Syntax_getArg(v___y_1970_, v___x_1981_);
v___x_1983_ = l_Lean_Syntax_isNone(v___x_1982_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
lean_inc(v___x_1982_);
v___x_1984_ = l_Lean_Syntax_matchesNull(v___x_1982_, v___x_1966_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v___x_1982_);
lean_dec(v_o_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1986_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1230_);
lean_dec(v___x_1982_);
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_1988_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1987_);
lean_inc(v___x_1986_);
v___x_1989_ = l_Lean_Syntax_isOfKind(v___x_1986_, v___x_1988_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec(v___x_1986_);
lean_dec(v_o_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_1990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v_args_1992_; lean_object* v___x_1993_; 
v___x_1991_ = l_Lean_Syntax_getArg(v___x_1986_, v___x_1966_);
lean_dec(v___x_1986_);
v_args_1992_ = l_Lean_Syntax_getArgs(v___x_1991_);
lean_dec(v___x_1991_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_args_1992_);
v___y_1940_ = v_o_1972_;
v___y_1941_ = v___y_1968_;
v___y_1942_ = v___y_1969_;
v___y_1943_ = v___y_1970_;
v___y_1944_ = v___y_1971_;
v_args_1945_ = v___x_1993_;
v___y_1946_ = v___y_1973_;
v___y_1947_ = v___y_1974_;
v___y_1948_ = v___y_1975_;
v___y_1949_ = v___y_1976_;
v___y_1950_ = v___y_1977_;
v___y_1951_ = v___y_1978_;
v___y_1952_ = v___y_1979_;
v___y_1953_ = v___y_1980_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v___x_1982_);
v___x_1994_ = lean_box(0);
v___y_1940_ = v_o_1972_;
v___y_1941_ = v___y_1968_;
v___y_1942_ = v___y_1969_;
v___y_1943_ = v___y_1970_;
v___y_1944_ = v___y_1971_;
v_args_1945_ = v___x_1994_;
v___y_1946_ = v___y_1973_;
v___y_1947_ = v___y_1974_;
v___y_1948_ = v___y_1975_;
v___y_1949_ = v___y_1976_;
v___y_1950_ = v___y_1977_;
v___y_1951_ = v___y_1978_;
v___y_1952_ = v___y_1979_;
v___y_1953_ = v___y_1980_;
goto v___jp_1939_;
}
}
v___jp_1995_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2005_ = lean_unsigned_to_nat(2u);
v___x_2006_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_2005_);
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_2008_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_2007_);
lean_inc(v___x_2006_);
v___x_2009_ = l_Lean_Syntax_isOfKind(v___x_2006_, v___x_2008_);
lean_dec(v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec(v___x_2006_);
lean_dec(v_bang_1996_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2010_;
}
else
{
lean_object* v_cfg_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_cfg_2011_ = l_Lean_Syntax_getArg(v___x_2006_, v___x_1230_);
v___x_2012_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_2013_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_2012_);
lean_inc(v_cfg_2011_);
v___x_2014_ = l_Lean_Syntax_isOfKind(v_cfg_2011_, v___x_2013_);
lean_dec(v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_cfg_2011_);
lean_dec(v___x_2006_);
lean_dec(v_bang_1996_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = l_Lean_Syntax_getArg(v___x_2006_, v___x_1966_);
v___x_2017_ = l_Lean_Syntax_getArg(v___x_2006_, v___x_2005_);
v___x_2018_ = l_Lean_Syntax_isNone(v___x_2017_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; 
lean_inc(v___x_2017_);
v___x_2019_ = l_Lean_Syntax_matchesNull(v___x_2017_, v___x_1966_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v___x_2017_);
lean_dec(v___x_2016_);
lean_dec(v_cfg_2011_);
lean_dec(v___x_2006_);
lean_dec(v_bang_1996_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2020_;
}
else
{
lean_object* v_o_2021_; lean_object* v___x_2022_; 
v_o_2021_ = l_Lean_Syntax_getArg(v___x_2017_, v___x_1230_);
lean_dec(v___x_2017_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_o_2021_);
v___y_1968_ = v___x_2016_;
v___y_1969_ = v_bang_1996_;
v___y_1970_ = v___x_2006_;
v___y_1971_ = v_cfg_2011_;
v_o_1972_ = v___x_2022_;
v___y_1973_ = v___y_1997_;
v___y_1974_ = v___y_1998_;
v___y_1975_ = v___y_1999_;
v___y_1976_ = v___y_2000_;
v___y_1977_ = v___y_2001_;
v___y_1978_ = v___y_2002_;
v___y_1979_ = v___y_2003_;
v___y_1980_ = v___y_2004_;
goto v___jp_1967_;
}
}
else
{
lean_object* v___x_2023_; 
lean_dec(v___x_2017_);
v___x_2023_ = lean_box(0);
v___y_1968_ = v___x_2016_;
v___y_1969_ = v_bang_1996_;
v___y_1970_ = v___x_2006_;
v___y_1971_ = v_cfg_2011_;
v_o_1972_ = v___x_2023_;
v___y_1973_ = v___y_1997_;
v___y_1974_ = v___y_1998_;
v___y_1975_ = v___y_1999_;
v___y_1976_ = v___y_2000_;
v___y_1977_ = v___y_2001_;
v___y_1978_ = v___y_2002_;
v___y_1979_ = v___y_2003_;
v___y_1980_ = v___y_2004_;
goto v___jp_1967_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2031_, lean_object* v_stx_2032_, lean_object* v___x_2033_, lean_object* v___x_2034_, lean_object* v___x_2035_, lean_object* v___x_2036_, lean_object* v___f_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v___x_35358__boxed_2047_; uint8_t v___x_35359__boxed_2048_; lean_object* v_res_2049_; 
v___x_35358__boxed_2047_ = lean_unbox(v___x_2031_);
v___x_35359__boxed_2048_ = lean_unbox(v___x_2033_);
v_res_2049_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35358__boxed_2047_, v_stx_2032_, v___x_35359__boxed_2048_, v___x_2034_, v___x_2035_, v___x_2036_, v___f_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v_stx_2032_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___y_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2072_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2059_);
v___x_2073_ = l_Lean_Syntax_isOfKind(v_stx_2059_, v___x_2072_);
v___x_2074_ = 1;
v___f_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2076_ = lean_box(v___x_2073_);
v___x_2077_ = lean_box(v___x_2074_);
v___y_2078_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2078_, 0, v___x_2076_);
lean_closure_set(v___y_2078_, 1, v_stx_2059_);
lean_closure_set(v___y_2078_, 2, v___x_2077_);
lean_closure_set(v___y_2078_, 3, v___x_2069_);
lean_closure_set(v___y_2078_, 4, v___x_2070_);
lean_closure_set(v___y_2078_, 5, v___x_2071_);
lean_closure_set(v___y_2078_, 6, v___f_2075_);
v___x_2079_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2079_, 0, v___y_2078_);
v___x_2080_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2079_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2092_, lean_object* v_as_2093_, lean_object* v_as_x27_2094_, lean_object* v_b_2095_, lean_object* v_a_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2092_, v_as_x27_2094_, v_b_2095_, v___y_2103_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2107_, lean_object* v_as_2108_, lean_object* v_as_x27_2109_, lean_object* v_b_2110_, lean_object* v_a_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2107_, v_as_2108_, v_as_x27_2109_, v_b_2110_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v_as_x27_2109_);
lean_dec(v_as_2108_);
lean_dec(v___x_2107_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2122_, lean_object* v_ref_2123_, lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2123_, v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_ref_2136_, lean_object* v_msg_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2135_, v_ref_2136_, v_msg_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v_ref_2136_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2148_, lean_object* v_ref_2149_, lean_object* v_constName_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2149_, v_constName_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_ref_2162_, lean_object* v_constName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2161_, v_ref_2162_, v_constName_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_ref_2162_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2175_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2198_, v___y_2205_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec_ref(v_opt_2209_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2220_, lean_object* v_ref_2221_, lean_object* v_msg_2222_, lean_object* v_declHint_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2221_, v_msg_2222_, v_declHint_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_ref_2235_, lean_object* v_msg_2236_, lean_object* v_declHint_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2234_, v_ref_2235_, v_msg_2236_, v_declHint_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v_ref_2235_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2248_, lean_object* v_declHint_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2248_, v_declHint_2249_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2260_, lean_object* v_declHint_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2260_, v_declHint_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2272_, lean_object* v_msgData_2273_, uint8_t v_severity_2274_, uint8_t v_isSilent_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2272_, v_msgData_2273_, v_severity_2274_, v_isSilent_2275_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2286_, lean_object* v_msgData_2287_, lean_object* v_severity_2288_, lean_object* v_isSilent_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_severity_boxed_2299_; uint8_t v_isSilent_boxed_2300_; lean_object* v_res_2301_; 
v_severity_boxed_2299_ = lean_unbox(v_severity_2288_);
v_isSilent_boxed_2300_ = lean_unbox(v_isSilent_2289_);
v_res_2301_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2286_, v_msgData_2287_, v_severity_boxed_2299_, v_isSilent_boxed_2300_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v_ref_2286_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2309_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2313_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2344_ = l_Lean_addBuiltinDeclarationRanges(v___x_2342_, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2347_, lean_object* v_as_x27_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_){
_start:
{
if (lean_obj_tag(v_as_x27_2348_) == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_b_2349_);
return v___x_2352_;
}
else
{
lean_object* v_head_2353_; lean_object* v_tail_2354_; lean_object* v_ref_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_head_2353_ = lean_ctor_get(v_as_x27_2348_, 0);
v_tail_2354_ = lean_ctor_get(v_as_x27_2348_, 1);
v_ref_2355_ = lean_ctor_get(v___y_2350_, 2);
v___x_2356_ = 1;
v___x_2357_ = 0;
v___x_2358_ = l_Lean_SourceInfo_fromRef(v_ref_2355_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2360_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2361_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2358_);
v___x_2362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2358_);
lean_ctor_set(v___x_2362_, 1, v___x_2360_);
lean_ctor_set(v___x_2362_, 2, v___x_2361_);
lean_inc(v_head_2353_);
v___x_2363_ = l_Lean_mkCIdentFrom(v___x_2347_, v_head_2353_, v___x_2356_);
lean_inc_ref(v___x_2362_);
v___x_2364_ = l_Lean_Syntax_node3(v___x_2358_, v___x_2359_, v___x_2362_, v___x_2362_, v___x_2363_);
v___x_2365_ = lean_array_push(v_b_2349_, v___x_2364_);
v_as_x27_2348_ = v_tail_2354_;
v_b_2349_ = v___x_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2367_, lean_object* v_as_x27_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2367_, v_as_x27_2368_, v_b_2369_, v___y_2370_);
lean_dec_ref(v___y_2370_);
lean_dec(v_as_x27_2368_);
lean_dec(v___x_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_b_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_b_2376_);
return v___x_2387_;
}
else
{
lean_object* v_a_2388_; lean_object* v_name_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2388_ = lean_array_uget_borrowed(v_as_2373_, v_i_2375_);
v_name_2389_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_name_2389_);
v___x_2390_ = l_Lean_mkIdent(v_name_2389_);
lean_inc(v___x_2390_);
v___x_2391_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2390_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2390_, v_a_2392_, v_b_2376_, v___y_2383_);
lean_dec(v_a_2392_);
lean_dec(v___x_2390_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; size_t v___x_2395_; size_t v___x_2396_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_add(v_i_2375_, v___x_2395_);
v_i_2375_ = v___x_2396_;
v_b_2376_ = v_a_2394_;
goto _start;
}
else
{
return v___x_2393_;
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v___x_2390_);
lean_dec_ref(v_b_2376_);
v_a_2398_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2391_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2391_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2406_, lean_object* v_sz_2407_, lean_object* v_i_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
size_t v_sz_boxed_2419_; size_t v_i_boxed_2420_; lean_object* v_res_2421_; 
v_sz_boxed_2419_ = lean_unbox_usize(v_sz_2407_);
lean_dec(v_sz_2407_);
v_i_boxed_2420_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_res_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2406_, v_sz_boxed_2419_, v_i_boxed_2420_, v_b_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v_as_2406_);
return v_res_2421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2424_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(32u);
v___x_2428_ = lean_mk_empty_array_with_capacity(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2430_ = ((size_t)5ULL);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_unsigned_to_nat(32u);
v___x_2433_ = lean_mk_empty_array_with_capacity(v___x_2432_);
v___x_2434_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2435_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___x_2433_);
lean_ctor_set(v___x_2435_, 2, v___x_2431_);
lean_ctor_set(v___x_2435_, 3, v___x_2431_);
lean_ctor_set_usize(v___x_2435_, 4, v___x_2430_);
return v___x_2435_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2437_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
lean_ctor_set(v___x_2438_, 2, v___x_2437_);
lean_ctor_set(v___x_2438_, 3, v___x_2436_);
return v___x_2438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2440_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___x_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2450_, lean_object* v_stx_2451_, uint8_t v___x_2452_, lean_object* v___x_2453_, lean_object* v___x_2454_, lean_object* v___x_2455_, lean_object* v___f_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
if (v___x_2450_ == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_2466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v_tk_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2583_; uint8_t v___y_2584_; lean_object* v___y_2585_; lean_object* v_stxForSuggestion_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; uint8_t v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; uint8_t v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; uint8_t v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; uint8_t v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2840_; uint8_t v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v_stxForExecution_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3146_; uint8_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v_argsArray_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v_args_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___x_3338_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v_o_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v_bang_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v_tk_2468_ = l_Lean_Syntax_getArg(v_stx_2451_, v___x_2467_);
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3396_ = l_Lean_Syntax_getArg(v_stx_2451_, v___x_3338_);
v___x_3397_ = l_Lean_Syntax_isNone(v___x_3396_);
if (v___x_3397_ == 0)
{
uint8_t v___x_3398_; 
lean_inc(v___x_3396_);
v___x_3398_ = l_Lean_Syntax_matchesNull(v___x_3396_, v___x_3338_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_dec(v___x_3396_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3399_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3399_;
}
else
{
lean_object* v_bang_3400_; lean_object* v___x_3401_; 
v_bang_3400_ = l_Lean_Syntax_getArg(v___x_3396_, v___x_2467_);
lean_dec(v___x_3396_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_bang_3400_);
v_bang_3368_ = v___x_3401_;
v___y_3369_ = v___y_2457_;
v___y_3370_ = v___y_2458_;
v___y_3371_ = v___y_2459_;
v___y_3372_ = v___y_2460_;
v___y_3373_ = v___y_2461_;
v___y_3374_ = v___y_2462_;
v___y_3375_ = v___y_2463_;
v___y_3376_ = v___y_2464_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3402_; 
lean_dec(v___x_3396_);
v___x_3402_ = lean_box(0);
v_bang_3368_ = v___x_3402_;
v___y_3369_ = v___y_2457_;
v___y_3370_ = v___y_2458_;
v___y_3371_ = v___y_2459_;
v___y_3372_ = v___y_2460_;
v___y_3373_ = v___y_2461_;
v___y_3374_ = v___y_2462_;
v___y_3375_ = v___y_2463_;
v___y_3376_ = v___y_2464_;
goto v___jp_3367_;
}
v___jp_2469_:
{
lean_object* v_usedTheorems_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2519_; 
v_usedTheorems_2476_ = lean_ctor_get(v___y_2471_, 0);
v_diag_2477_ = lean_ctor_get(v___y_2471_, 1);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___y_2471_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2479_ = v___y_2471_;
v_isShared_2480_ = v_isSharedCheck_2519_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_usedTheorems_2476_);
lean_dec(v___y_2471_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2519_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2470_, v_usedTheorems_2476_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec_ref(v_usedTheorems_2476_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v_ref_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v_ref_2483_ = lean_ctor_get(v___y_2474_, 2);
v___x_2484_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v_a_2482_);
lean_ctor_set(v___x_2479_, 0, v___x_2484_);
v___x_2486_ = v___x_2479_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_a_2482_);
v___x_2486_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
lean_ctor_set(v___x_2488_, 3, v___x_2487_);
lean_ctor_set(v___x_2488_, 4, v___x_2487_);
lean_ctor_set(v___x_2488_, 5, v___x_2487_);
lean_inc(v_ref_2483_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_ref_2483_);
v___x_2490_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2491_ = 4;
v___x_2492_ = l_Lean_MessageData_nil;
v___x_2493_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2468_, v___x_2488_, v___x_2489_, v___x_2490_, v___x_2487_, v___x_2491_, v___x_2492_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2493_, 0);
lean_dec(v_unused_2501_);
v___x_2495_ = v___x_2493_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v___x_2493_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_diag_2477_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_diag_2477_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref(v_diag_2477_);
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_del_object(v___x_2479_);
lean_dec_ref(v_diag_2477_);
lean_dec(v_tk_2468_);
v_a_2511_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2481_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2481_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
v___jp_2520_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2527_, v___y_2523_, v___y_2525_, v___y_2524_, v___y_2521_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2532_ = l_Lean_Meta_simpAll(v_a_2530_, v___y_2528_, v___y_2522_, v___x_2531_, v___y_2523_, v___y_2525_, v___y_2524_, v___y_2521_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_fst_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v_fst_2534_ = lean_ctor_get(v_a_2533_, 0);
if (lean_obj_tag(v_fst_2534_) == 0)
{
lean_object* v_snd_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_snd_2535_ = lean_ctor_get(v_a_2533_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_a_2533_);
v___x_2536_ = lean_box(0);
v___x_2537_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2536_, v___y_2527_, v___y_2523_, v___y_2525_, v___y_2524_, v___y_2521_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2470_ = v___y_2526_;
v___y_2471_ = v_snd_2535_;
v___y_2472_ = v___y_2523_;
v___y_2473_ = v___y_2525_;
v___y_2474_ = v___y_2524_;
v___y_2475_ = v___y_2521_;
goto v___jp_2469_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_snd_2535_);
lean_dec(v___y_2526_);
lean_dec(v_tk_2468_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_snd_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2564_; 
lean_inc_ref(v_fst_2534_);
v_snd_2546_ = lean_ctor_get(v_a_2533_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v_a_2533_, 0);
lean_dec(v_unused_2565_);
v___x_2548_ = v_a_2533_;
v_isShared_2549_ = v_isSharedCheck_2564_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_snd_2546_);
lean_dec(v_a_2533_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2564_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_val_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_val_2550_ = lean_ctor_get(v_fst_2534_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v_fst_2534_, 1);
v___x_2551_ = lean_box(0);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 1);
lean_ctor_set(v___x_2548_, 1, v___x_2551_);
lean_ctor_set(v___x_2548_, 0, v_val_2550_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_val_2550_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2553_, v___y_2527_, v___y_2523_, v___y_2525_, v___y_2524_, v___y_2521_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_dec_ref_known(v___x_2554_, 1);
v___y_2470_ = v___y_2526_;
v___y_2471_ = v_snd_2546_;
v___y_2472_ = v___y_2523_;
v___y_2473_ = v___y_2525_;
v___y_2474_ = v___y_2524_;
v___y_2475_ = v___y_2521_;
goto v___jp_2469_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_snd_2546_);
lean_dec(v___y_2526_);
lean_dec(v_tk_2468_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v___y_2526_);
lean_dec(v_tk_2468_);
v_a_2566_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2532_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2532_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2522_);
lean_dec(v_tk_2468_);
v_a_2574_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2529_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2529_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
v___jp_2582_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2596_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2585_, v___x_2452_, v___y_2584_, v___x_2452_, v___x_2595_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2585_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
if (lean_obj_tag(v___y_2583_) == 0)
{
lean_object* v_ctx_2598_; lean_object* v_simprocs_2599_; 
v_ctx_2598_ = lean_ctor_get(v_a_2597_, 0);
lean_inc_ref(v_ctx_2598_);
v_simprocs_2599_ = lean_ctor_get(v_a_2597_, 1);
lean_inc_ref(v_simprocs_2599_);
lean_dec(v_a_2597_);
v___y_2521_ = v___y_2594_;
v___y_2522_ = v_simprocs_2599_;
v___y_2523_ = v___y_2591_;
v___y_2524_ = v___y_2593_;
v___y_2525_ = v___y_2592_;
v___y_2526_ = v_stxForSuggestion_2586_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v_ctx_2598_;
goto v___jp_2520_;
}
else
{
lean_object* v_ctx_2600_; lean_object* v_simprocs_2601_; lean_object* v___x_2602_; 
lean_dec_ref_known(v___y_2583_, 1);
v_ctx_2600_ = lean_ctor_get(v_a_2597_, 0);
lean_inc_ref(v_ctx_2600_);
v_simprocs_2601_ = lean_ctor_get(v_a_2597_, 1);
lean_inc_ref(v_simprocs_2601_);
lean_dec(v_a_2597_);
v___x_2602_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2600_);
v___y_2521_ = v___y_2594_;
v___y_2522_ = v_simprocs_2601_;
v___y_2523_ = v___y_2591_;
v___y_2524_ = v___y_2593_;
v___y_2525_ = v___y_2592_;
v___y_2526_ = v_stxForSuggestion_2586_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v___x_2602_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_stxForSuggestion_2586_);
lean_dec(v___y_2583_);
lean_dec(v_tk_2468_);
v_a_2603_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2596_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2596_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
v___jp_2611_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_inc_ref_n(v___y_2625_, 2);
v___x_2632_ = l_Array_append___redArg(v___y_2625_, v___y_2631_);
lean_dec_ref(v___y_2631_);
lean_inc_n(v___y_2623_, 3);
lean_inc_n(v___y_2617_, 5);
v___x_2633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___y_2617_);
lean_ctor_set(v___x_2633_, 1, v___y_2623_);
lean_ctor_set(v___x_2633_, 2, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___y_2617_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2637_ = l_Lean_Syntax_SepArray_ofElems(v___x_2636_, v___y_2630_);
lean_dec_ref(v___y_2630_);
v___x_2638_ = l_Array_append___redArg(v___y_2625_, v___x_2637_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2639_, 0, v___y_2617_);
lean_ctor_set(v___x_2639_, 1, v___y_2623_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2617_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_Syntax_node3(v___y_2617_, v___y_2623_, v___x_2635_, v___x_2639_, v___x_2641_);
v___x_2643_ = l_Lean_Syntax_node5(v___y_2617_, v___y_2618_, v___y_2621_, v___y_2616_, v___y_2619_, v___x_2633_, v___x_2642_);
v___y_2583_ = v___y_2612_;
v___y_2584_ = v___y_2622_;
v___y_2585_ = v___y_2615_;
v_stxForSuggestion_2586_ = v___x_2643_;
v___y_2587_ = v___y_2624_;
v___y_2588_ = v___y_2628_;
v___y_2589_ = v___y_2626_;
v___y_2590_ = v___y_2613_;
v___y_2591_ = v___y_2629_;
v___y_2592_ = v___y_2614_;
v___y_2593_ = v___y_2627_;
v___y_2594_ = v___y_2620_;
goto v___jp_2582_;
}
v___jp_2644_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_inc_ref(v___y_2659_);
v___x_2665_ = l_Array_append___redArg(v___y_2659_, v___y_2664_);
lean_dec_ref(v___y_2664_);
lean_inc(v___y_2655_);
lean_inc(v___y_2651_);
v___x_2666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2666_, 0, v___y_2651_);
lean_ctor_set(v___x_2666_, 1, v___y_2655_);
lean_ctor_set(v___x_2666_, 2, v___x_2665_);
if (lean_obj_tag(v___y_2647_) == 1)
{
lean_object* v_val_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_val_2667_ = lean_ctor_get(v___y_2647_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v___y_2647_, 1);
v___x_2668_ = l_Lean_SourceInfo_fromRef(v_val_2667_, v___x_2452_);
lean_dec(v_val_2667_);
v___x_2669_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Array_mkArray1___redArg(v___x_2670_);
v___y_2612_ = v___y_2645_;
v___y_2613_ = v___y_2646_;
v___y_2614_ = v___y_2648_;
v___y_2615_ = v___y_2649_;
v___y_2616_ = v___y_2650_;
v___y_2617_ = v___y_2651_;
v___y_2618_ = v___y_2652_;
v___y_2619_ = v___x_2666_;
v___y_2620_ = v___y_2653_;
v___y_2621_ = v___y_2654_;
v___y_2622_ = v___y_2656_;
v___y_2623_ = v___y_2655_;
v___y_2624_ = v___y_2657_;
v___y_2625_ = v___y_2659_;
v___y_2626_ = v___y_2658_;
v___y_2627_ = v___y_2660_;
v___y_2628_ = v___y_2661_;
v___y_2629_ = v___y_2662_;
v___y_2630_ = v___y_2663_;
v___y_2631_ = v___x_2671_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2672_; 
lean_dec(v___y_2647_);
v___x_2672_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2612_ = v___y_2645_;
v___y_2613_ = v___y_2646_;
v___y_2614_ = v___y_2648_;
v___y_2615_ = v___y_2649_;
v___y_2616_ = v___y_2650_;
v___y_2617_ = v___y_2651_;
v___y_2618_ = v___y_2652_;
v___y_2619_ = v___x_2666_;
v___y_2620_ = v___y_2653_;
v___y_2621_ = v___y_2654_;
v___y_2622_ = v___y_2656_;
v___y_2623_ = v___y_2655_;
v___y_2624_ = v___y_2657_;
v___y_2625_ = v___y_2659_;
v___y_2626_ = v___y_2658_;
v___y_2627_ = v___y_2660_;
v___y_2628_ = v___y_2661_;
v___y_2629_ = v___y_2662_;
v___y_2630_ = v___y_2663_;
v___y_2631_ = v___x_2672_;
goto v___jp_2611_;
}
}
v___jp_2673_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_inc_ref_n(v___y_2674_, 2);
v___x_2694_ = l_Array_append___redArg(v___y_2674_, v___y_2693_);
lean_dec_ref(v___y_2693_);
lean_inc_n(v___y_2677_, 3);
lean_inc_n(v___y_2684_, 5);
v___x_2695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2684_);
lean_ctor_set(v___x_2695_, 1, v___y_2677_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
v___x_2696_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2684_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2699_ = l_Lean_Syntax_SepArray_ofElems(v___x_2698_, v___y_2692_);
lean_dec_ref(v___y_2692_);
v___x_2700_ = l_Array_append___redArg(v___y_2674_, v___x_2699_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2684_);
lean_ctor_set(v___x_2701_, 1, v___y_2677_);
lean_ctor_set(v___x_2701_, 2, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2684_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_Syntax_node3(v___y_2684_, v___y_2677_, v___x_2697_, v___x_2701_, v___x_2703_);
v___x_2705_ = l_Lean_Syntax_node5(v___y_2684_, v___y_2681_, v___y_2679_, v___y_2683_, v___y_2682_, v___x_2695_, v___x_2704_);
v___y_2583_ = v___y_2675_;
v___y_2584_ = v___y_2686_;
v___y_2585_ = v___y_2680_;
v_stxForSuggestion_2586_ = v___x_2705_;
v___y_2587_ = v___y_2687_;
v___y_2588_ = v___y_2690_;
v___y_2589_ = v___y_2688_;
v___y_2590_ = v___y_2676_;
v___y_2591_ = v___y_2691_;
v___y_2592_ = v___y_2678_;
v___y_2593_ = v___y_2689_;
v___y_2594_ = v___y_2685_;
goto v___jp_2582_;
}
v___jp_2706_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_inc_ref(v___y_2707_);
v___x_2727_ = l_Array_append___redArg(v___y_2707_, v___y_2726_);
lean_dec_ref(v___y_2726_);
lean_inc(v___y_2711_);
lean_inc(v___y_2717_);
v___x_2728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2728_, 0, v___y_2717_);
lean_ctor_set(v___x_2728_, 1, v___y_2711_);
lean_ctor_set(v___x_2728_, 2, v___x_2727_);
if (lean_obj_tag(v___y_2710_) == 1)
{
lean_object* v_val_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_val_2729_ = lean_ctor_get(v___y_2710_, 0);
lean_inc(v_val_2729_);
lean_dec_ref_known(v___y_2710_, 1);
v___x_2730_ = l_Lean_SourceInfo_fromRef(v_val_2729_, v___x_2452_);
lean_dec(v_val_2729_);
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = l_Array_mkArray1___redArg(v___x_2732_);
v___y_2674_ = v___y_2707_;
v___y_2675_ = v___y_2708_;
v___y_2676_ = v___y_2709_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2712_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2714_;
v___y_2681_ = v___y_2715_;
v___y_2682_ = v___x_2728_;
v___y_2683_ = v___y_2716_;
v___y_2684_ = v___y_2717_;
v___y_2685_ = v___y_2718_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___y_2722_;
v___y_2690_ = v___y_2723_;
v___y_2691_ = v___y_2724_;
v___y_2692_ = v___y_2725_;
v___y_2693_ = v___x_2733_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2734_; 
lean_dec(v___y_2710_);
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2674_ = v___y_2707_;
v___y_2675_ = v___y_2708_;
v___y_2676_ = v___y_2709_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2712_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2714_;
v___y_2681_ = v___y_2715_;
v___y_2682_ = v___x_2728_;
v___y_2683_ = v___y_2716_;
v___y_2684_ = v___y_2717_;
v___y_2685_ = v___y_2718_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___y_2722_;
v___y_2690_ = v___y_2723_;
v___y_2691_ = v___y_2724_;
v___y_2692_ = v___y_2725_;
v___y_2693_ = v___x_2734_;
goto v___jp_2673_;
}
}
v___jp_2735_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_inc_ref_n(v___y_2743_, 2);
v___x_2755_ = l_Array_append___redArg(v___y_2743_, v___y_2754_);
lean_dec_ref(v___y_2754_);
lean_inc_n(v___y_2753_, 2);
lean_inc_n(v___y_2744_, 2);
v___x_2756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2744_);
lean_ctor_set(v___x_2756_, 1, v___y_2753_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2744_);
lean_ctor_set(v___x_2757_, 1, v___y_2753_);
lean_ctor_set(v___x_2757_, 2, v___y_2743_);
v___x_2758_ = l_Lean_Syntax_node5(v___y_2744_, v___y_2746_, v___y_2752_, v___y_2741_, v___y_2740_, v___x_2756_, v___x_2757_);
v___y_2583_ = v___y_2736_;
v___y_2584_ = v___y_2745_;
v___y_2585_ = v___y_2739_;
v_stxForSuggestion_2586_ = v___x_2758_;
v___y_2587_ = v___y_2747_;
v___y_2588_ = v___y_2750_;
v___y_2589_ = v___y_2748_;
v___y_2590_ = v___y_2737_;
v___y_2591_ = v___y_2751_;
v___y_2592_ = v___y_2738_;
v___y_2593_ = v___y_2749_;
v___y_2594_ = v___y_2742_;
goto v___jp_2582_;
}
v___jp_2759_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_inc_ref(v___y_2766_);
v___x_2779_ = l_Array_append___redArg(v___y_2766_, v___y_2778_);
lean_dec_ref(v___y_2778_);
lean_inc(v___y_2777_);
lean_inc(v___y_2768_);
v___x_2780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2780_, 0, v___y_2768_);
lean_ctor_set(v___x_2780_, 1, v___y_2777_);
lean_ctor_set(v___x_2780_, 2, v___x_2779_);
if (lean_obj_tag(v___y_2762_) == 1)
{
lean_object* v_val_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_val_2781_ = lean_ctor_get(v___y_2762_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___y_2762_, 1);
v___x_2782_ = l_Lean_SourceInfo_fromRef(v_val_2781_, v___x_2452_);
lean_dec(v_val_2781_);
v___x_2783_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Array_mkArray1___redArg(v___x_2784_);
v___y_2736_ = v___y_2760_;
v___y_2737_ = v___y_2761_;
v___y_2738_ = v___y_2763_;
v___y_2739_ = v___y_2764_;
v___y_2740_ = v___x_2780_;
v___y_2741_ = v___y_2765_;
v___y_2742_ = v___y_2767_;
v___y_2743_ = v___y_2766_;
v___y_2744_ = v___y_2768_;
v___y_2745_ = v___y_2769_;
v___y_2746_ = v___y_2770_;
v___y_2747_ = v___y_2771_;
v___y_2748_ = v___y_2772_;
v___y_2749_ = v___y_2773_;
v___y_2750_ = v___y_2774_;
v___y_2751_ = v___y_2775_;
v___y_2752_ = v___y_2776_;
v___y_2753_ = v___y_2777_;
v___y_2754_ = v___x_2785_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2786_; 
lean_dec(v___y_2762_);
v___x_2786_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2736_ = v___y_2760_;
v___y_2737_ = v___y_2761_;
v___y_2738_ = v___y_2763_;
v___y_2739_ = v___y_2764_;
v___y_2740_ = v___x_2780_;
v___y_2741_ = v___y_2765_;
v___y_2742_ = v___y_2767_;
v___y_2743_ = v___y_2766_;
v___y_2744_ = v___y_2768_;
v___y_2745_ = v___y_2769_;
v___y_2746_ = v___y_2770_;
v___y_2747_ = v___y_2771_;
v___y_2748_ = v___y_2772_;
v___y_2749_ = v___y_2773_;
v___y_2750_ = v___y_2774_;
v___y_2751_ = v___y_2775_;
v___y_2752_ = v___y_2776_;
v___y_2753_ = v___y_2777_;
v___y_2754_ = v___x_2786_;
goto v___jp_2735_;
}
}
v___jp_2787_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_inc_ref_n(v___y_2793_, 2);
v___x_2807_ = l_Array_append___redArg(v___y_2793_, v___y_2806_);
lean_dec_ref(v___y_2806_);
lean_inc_n(v___y_2795_, 2);
lean_inc_n(v___y_2796_, 2);
v___x_2808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2808_, 0, v___y_2796_);
lean_ctor_set(v___x_2808_, 1, v___y_2795_);
lean_ctor_set(v___x_2808_, 2, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2809_, 0, v___y_2796_);
lean_ctor_set(v___x_2809_, 1, v___y_2795_);
lean_ctor_set(v___x_2809_, 2, v___y_2793_);
v___x_2810_ = l_Lean_Syntax_node5(v___y_2796_, v___y_2790_, v___y_2802_, v___y_2794_, v___y_2804_, v___x_2808_, v___x_2809_);
v___y_2583_ = v___y_2788_;
v___y_2584_ = v___y_2798_;
v___y_2585_ = v___y_2792_;
v_stxForSuggestion_2586_ = v___x_2810_;
v___y_2587_ = v___y_2799_;
v___y_2588_ = v___y_2803_;
v___y_2589_ = v___y_2800_;
v___y_2590_ = v___y_2789_;
v___y_2591_ = v___y_2805_;
v___y_2592_ = v___y_2791_;
v___y_2593_ = v___y_2801_;
v___y_2594_ = v___y_2797_;
goto v___jp_2582_;
}
v___jp_2811_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_inc_ref(v___y_2818_);
v___x_2831_ = l_Array_append___redArg(v___y_2818_, v___y_2830_);
lean_dec_ref(v___y_2830_);
lean_inc(v___y_2820_);
lean_inc(v___y_2821_);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___y_2821_);
lean_ctor_set(v___x_2832_, 1, v___y_2820_);
lean_ctor_set(v___x_2832_, 2, v___x_2831_);
if (lean_obj_tag(v___y_2814_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_val_2833_ = lean_ctor_get(v___y_2814_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v___y_2814_, 1);
v___x_2834_ = l_Lean_SourceInfo_fromRef(v_val_2833_, v___x_2452_);
lean_dec(v_val_2833_);
v___x_2835_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Array_mkArray1___redArg(v___x_2836_);
v___y_2788_ = v___y_2812_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
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
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2827_;
v___y_2804_ = v___x_2832_;
v___y_2805_ = v___y_2829_;
v___y_2806_ = v___x_2837_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2838_; 
lean_dec(v___y_2814_);
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2788_ = v___y_2812_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
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
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2827_;
v___y_2804_ = v___x_2832_;
v___y_2805_ = v___y_2829_;
v___y_2806_ = v___x_2838_;
goto v___jp_2787_;
}
}
v___jp_2839_:
{
lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2843_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = lean_array_get_size(v___y_2845_);
v___x_2858_ = lean_nat_dec_eq(v___x_2857_, v___x_2467_);
if (v___x_2858_ == 0)
{
if (lean_obj_tag(v___y_2840_) == 0)
{
lean_object* v_ref_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_ref_2859_ = lean_ctor_get(v___y_2853_, 2);
v___x_2860_ = l_Lean_SourceInfo_fromRef(v_ref_2859_, v___x_2858_);
v___x_2861_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2862_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_2861_);
v___x_2863_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_2864_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2867_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2844_) == 1)
{
lean_object* v_val_2868_; lean_object* v___x_2869_; 
v_val_2868_ = lean_ctor_get(v___y_2844_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v___y_2844_, 1);
v___x_2869_ = l_Array_mkArray1___redArg(v_val_2868_);
v___y_2645_ = v___y_2840_;
v___y_2646_ = v___y_2850_;
v___y_2647_ = v___y_2842_;
v___y_2648_ = v___y_2852_;
v___y_2649_ = v_stxForExecution_2846_;
v___y_2650_ = v_a_2856_;
v___y_2651_ = v___x_2860_;
v___y_2652_ = v___x_2862_;
v___y_2653_ = v___y_2854_;
v___y_2654_ = v___x_2865_;
v___y_2655_ = v___x_2866_;
v___y_2656_ = v___y_2841_;
v___y_2657_ = v___y_2847_;
v___y_2658_ = v___y_2849_;
v___y_2659_ = v___x_2867_;
v___y_2660_ = v___y_2853_;
v___y_2661_ = v___y_2848_;
v___y_2662_ = v___y_2851_;
v___y_2663_ = v___y_2845_;
v___y_2664_ = v___x_2869_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2870_; 
lean_dec(v___y_2844_);
v___x_2870_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2645_ = v___y_2840_;
v___y_2646_ = v___y_2850_;
v___y_2647_ = v___y_2842_;
v___y_2648_ = v___y_2852_;
v___y_2649_ = v_stxForExecution_2846_;
v___y_2650_ = v_a_2856_;
v___y_2651_ = v___x_2860_;
v___y_2652_ = v___x_2862_;
v___y_2653_ = v___y_2854_;
v___y_2654_ = v___x_2865_;
v___y_2655_ = v___x_2866_;
v___y_2656_ = v___y_2841_;
v___y_2657_ = v___y_2847_;
v___y_2658_ = v___y_2849_;
v___y_2659_ = v___x_2867_;
v___y_2660_ = v___y_2853_;
v___y_2661_ = v___y_2848_;
v___y_2662_ = v___y_2851_;
v___y_2663_ = v___y_2845_;
v___y_2664_ = v___x_2870_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_ref_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_ref_2871_ = lean_ctor_get(v___y_2853_, 2);
v___x_2872_ = l_Lean_SourceInfo_fromRef(v_ref_2871_, v___x_2858_);
v___x_2873_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2874_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_2873_);
v___x_2875_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2879_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2844_) == 1)
{
lean_object* v_val_2880_; lean_object* v___x_2881_; 
v_val_2880_ = lean_ctor_get(v___y_2844_, 0);
lean_inc(v_val_2880_);
lean_dec_ref_known(v___y_2844_, 1);
v___x_2881_ = l_Array_mkArray1___redArg(v_val_2880_);
v___y_2707_ = v___x_2879_;
v___y_2708_ = v___y_2840_;
v___y_2709_ = v___y_2850_;
v___y_2710_ = v___y_2842_;
v___y_2711_ = v___x_2878_;
v___y_2712_ = v___y_2852_;
v___y_2713_ = v___x_2877_;
v___y_2714_ = v_stxForExecution_2846_;
v___y_2715_ = v___x_2874_;
v___y_2716_ = v_a_2856_;
v___y_2717_ = v___x_2872_;
v___y_2718_ = v___y_2854_;
v___y_2719_ = v___y_2841_;
v___y_2720_ = v___y_2847_;
v___y_2721_ = v___y_2849_;
v___y_2722_ = v___y_2853_;
v___y_2723_ = v___y_2848_;
v___y_2724_ = v___y_2851_;
v___y_2725_ = v___y_2845_;
v___y_2726_ = v___x_2881_;
goto v___jp_2706_;
}
else
{
lean_object* v___x_2882_; 
lean_dec(v___y_2844_);
v___x_2882_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2707_ = v___x_2879_;
v___y_2708_ = v___y_2840_;
v___y_2709_ = v___y_2850_;
v___y_2710_ = v___y_2842_;
v___y_2711_ = v___x_2878_;
v___y_2712_ = v___y_2852_;
v___y_2713_ = v___x_2877_;
v___y_2714_ = v_stxForExecution_2846_;
v___y_2715_ = v___x_2874_;
v___y_2716_ = v_a_2856_;
v___y_2717_ = v___x_2872_;
v___y_2718_ = v___y_2854_;
v___y_2719_ = v___y_2841_;
v___y_2720_ = v___y_2847_;
v___y_2721_ = v___y_2849_;
v___y_2722_ = v___y_2853_;
v___y_2723_ = v___y_2848_;
v___y_2724_ = v___y_2851_;
v___y_2725_ = v___y_2845_;
v___y_2726_ = v___x_2882_;
goto v___jp_2706_;
}
}
}
else
{
lean_dec_ref(v___y_2845_);
if (lean_obj_tag(v___y_2840_) == 0)
{
lean_object* v_ref_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_ref_2883_ = lean_ctor_get(v___y_2853_, 2);
v___x_2884_ = 0;
v___x_2885_ = l_Lean_SourceInfo_fromRef(v_ref_2883_, v___x_2884_);
v___x_2886_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2887_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_2886_);
v___x_2888_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_2889_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2892_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2844_) == 1)
{
lean_object* v_val_2893_; lean_object* v___x_2894_; 
v_val_2893_ = lean_ctor_get(v___y_2844_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v___y_2844_, 1);
v___x_2894_ = l_Array_mkArray1___redArg(v_val_2893_);
v___y_2760_ = v___y_2840_;
v___y_2761_ = v___y_2850_;
v___y_2762_ = v___y_2842_;
v___y_2763_ = v___y_2852_;
v___y_2764_ = v_stxForExecution_2846_;
v___y_2765_ = v_a_2856_;
v___y_2766_ = v___x_2892_;
v___y_2767_ = v___y_2854_;
v___y_2768_ = v___x_2885_;
v___y_2769_ = v___y_2841_;
v___y_2770_ = v___x_2887_;
v___y_2771_ = v___y_2847_;
v___y_2772_ = v___y_2849_;
v___y_2773_ = v___y_2853_;
v___y_2774_ = v___y_2848_;
v___y_2775_ = v___y_2851_;
v___y_2776_ = v___x_2890_;
v___y_2777_ = v___x_2891_;
v___y_2778_ = v___x_2894_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2895_; 
lean_dec(v___y_2844_);
v___x_2895_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2760_ = v___y_2840_;
v___y_2761_ = v___y_2850_;
v___y_2762_ = v___y_2842_;
v___y_2763_ = v___y_2852_;
v___y_2764_ = v_stxForExecution_2846_;
v___y_2765_ = v_a_2856_;
v___y_2766_ = v___x_2892_;
v___y_2767_ = v___y_2854_;
v___y_2768_ = v___x_2885_;
v___y_2769_ = v___y_2841_;
v___y_2770_ = v___x_2887_;
v___y_2771_ = v___y_2847_;
v___y_2772_ = v___y_2849_;
v___y_2773_ = v___y_2853_;
v___y_2774_ = v___y_2848_;
v___y_2775_ = v___y_2851_;
v___y_2776_ = v___x_2890_;
v___y_2777_ = v___x_2891_;
v___y_2778_ = v___x_2895_;
goto v___jp_2759_;
}
}
else
{
lean_object* v_ref_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_ref_2896_ = lean_ctor_get(v___y_2853_, 2);
v___x_2897_ = 0;
v___x_2898_ = l_Lean_SourceInfo_fromRef(v_ref_2896_, v___x_2897_);
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2900_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_2899_);
v___x_2901_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_2902_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2905_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2844_) == 1)
{
lean_object* v_val_2906_; lean_object* v___x_2907_; 
v_val_2906_ = lean_ctor_get(v___y_2844_, 0);
lean_inc(v_val_2906_);
lean_dec_ref_known(v___y_2844_, 1);
v___x_2907_ = l_Array_mkArray1___redArg(v_val_2906_);
v___y_2812_ = v___y_2840_;
v___y_2813_ = v___y_2850_;
v___y_2814_ = v___y_2842_;
v___y_2815_ = v___x_2900_;
v___y_2816_ = v___y_2852_;
v___y_2817_ = v_stxForExecution_2846_;
v___y_2818_ = v___x_2905_;
v___y_2819_ = v_a_2856_;
v___y_2820_ = v___x_2904_;
v___y_2821_ = v___x_2898_;
v___y_2822_ = v___y_2854_;
v___y_2823_ = v___y_2841_;
v___y_2824_ = v___y_2847_;
v___y_2825_ = v___y_2849_;
v___y_2826_ = v___y_2853_;
v___y_2827_ = v___y_2848_;
v___y_2828_ = v___x_2903_;
v___y_2829_ = v___y_2851_;
v___y_2830_ = v___x_2907_;
goto v___jp_2811_;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v___y_2844_);
v___x_2908_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2812_ = v___y_2840_;
v___y_2813_ = v___y_2850_;
v___y_2814_ = v___y_2842_;
v___y_2815_ = v___x_2900_;
v___y_2816_ = v___y_2852_;
v___y_2817_ = v_stxForExecution_2846_;
v___y_2818_ = v___x_2905_;
v___y_2819_ = v_a_2856_;
v___y_2820_ = v___x_2904_;
v___y_2821_ = v___x_2898_;
v___y_2822_ = v___y_2854_;
v___y_2823_ = v___y_2841_;
v___y_2824_ = v___y_2847_;
v___y_2825_ = v___y_2849_;
v___y_2826_ = v___y_2853_;
v___y_2827_ = v___y_2848_;
v___y_2828_ = v___x_2903_;
v___y_2829_ = v___y_2851_;
v___y_2830_ = v___x_2908_;
goto v___jp_2811_;
}
}
}
}
v___jp_2909_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_inc_ref_n(v___y_2923_, 2);
v___x_2931_ = l_Array_append___redArg(v___y_2923_, v___y_2930_);
lean_dec_ref(v___y_2930_);
lean_inc_n(v___y_2928_, 3);
lean_inc_n(v___y_2925_, 5);
v___x_2932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2932_, 0, v___y_2925_);
lean_ctor_set(v___x_2932_, 1, v___y_2928_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___y_2925_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2936_ = l_Lean_Syntax_SepArray_ofElems(v___x_2935_, v___y_2929_);
v___x_2937_ = l_Array_append___redArg(v___y_2923_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2938_, 0, v___y_2925_);
lean_ctor_set(v___x_2938_, 1, v___y_2928_);
lean_ctor_set(v___x_2938_, 2, v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2925_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = l_Lean_Syntax_node3(v___y_2925_, v___y_2928_, v___x_2934_, v___x_2938_, v___x_2940_);
lean_inc(v___y_2914_);
v___x_2942_ = l_Lean_Syntax_node5(v___y_2925_, v___y_2912_, v___y_2926_, v___y_2914_, v___y_2922_, v___x_2932_, v___x_2941_);
v___y_2840_ = v___y_2911_;
v___y_2841_ = v___y_2919_;
v___y_2842_ = v___y_2913_;
v___y_2843_ = v___y_2914_;
v___y_2844_ = v___y_2921_;
v___y_2845_ = v___y_2929_;
v_stxForExecution_2846_ = v___x_2942_;
v___y_2847_ = v___y_2927_;
v___y_2848_ = v___y_2910_;
v___y_2849_ = v___y_2916_;
v___y_2850_ = v___y_2920_;
v___y_2851_ = v___y_2924_;
v___y_2852_ = v___y_2915_;
v___y_2853_ = v___y_2918_;
v___y_2854_ = v___y_2917_;
goto v___jp_2839_;
}
v___jp_2943_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_inc_ref(v___y_2956_);
v___x_2964_ = l_Array_append___redArg(v___y_2956_, v___y_2963_);
lean_dec_ref(v___y_2963_);
lean_inc(v___y_2961_);
lean_inc(v___y_2959_);
v___x_2965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2965_, 0, v___y_2959_);
lean_ctor_set(v___x_2965_, 1, v___y_2961_);
lean_ctor_set(v___x_2965_, 2, v___x_2964_);
if (lean_obj_tag(v___y_2947_) == 1)
{
lean_object* v_val_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_val_2966_ = lean_ctor_get(v___y_2947_, 0);
v___x_2967_ = l_Lean_SourceInfo_fromRef(v_val_2966_, v___x_2452_);
v___x_2968_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = l_Array_mkArray1___redArg(v___x_2969_);
v___y_2910_ = v___y_2944_;
v___y_2911_ = v___y_2945_;
v___y_2912_ = v___y_2946_;
v___y_2913_ = v___y_2947_;
v___y_2914_ = v___y_2948_;
v___y_2915_ = v___y_2949_;
v___y_2916_ = v___y_2950_;
v___y_2917_ = v___y_2951_;
v___y_2918_ = v___y_2952_;
v___y_2919_ = v___y_2954_;
v___y_2920_ = v___y_2953_;
v___y_2921_ = v___y_2955_;
v___y_2922_ = v___x_2965_;
v___y_2923_ = v___y_2956_;
v___y_2924_ = v___y_2957_;
v___y_2925_ = v___y_2959_;
v___y_2926_ = v___y_2958_;
v___y_2927_ = v___y_2960_;
v___y_2928_ = v___y_2961_;
v___y_2929_ = v___y_2962_;
v___y_2930_ = v___x_2970_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2971_; 
v___x_2971_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2910_ = v___y_2944_;
v___y_2911_ = v___y_2945_;
v___y_2912_ = v___y_2946_;
v___y_2913_ = v___y_2947_;
v___y_2914_ = v___y_2948_;
v___y_2915_ = v___y_2949_;
v___y_2916_ = v___y_2950_;
v___y_2917_ = v___y_2951_;
v___y_2918_ = v___y_2952_;
v___y_2919_ = v___y_2954_;
v___y_2920_ = v___y_2953_;
v___y_2921_ = v___y_2955_;
v___y_2922_ = v___x_2965_;
v___y_2923_ = v___y_2956_;
v___y_2924_ = v___y_2957_;
v___y_2925_ = v___y_2959_;
v___y_2926_ = v___y_2958_;
v___y_2927_ = v___y_2960_;
v___y_2928_ = v___y_2961_;
v___y_2929_ = v___y_2962_;
v___y_2930_ = v___x_2971_;
goto v___jp_2909_;
}
}
v___jp_2972_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_inc_ref_n(v___y_2983_, 2);
v___x_2994_ = l_Array_append___redArg(v___y_2983_, v___y_2993_);
lean_dec_ref(v___y_2993_);
lean_inc_n(v___y_2980_, 3);
lean_inc_n(v___y_2982_, 5);
v___x_2995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2995_, 0, v___y_2982_);
lean_ctor_set(v___x_2995_, 1, v___y_2980_);
lean_ctor_set(v___x_2995_, 2, v___x_2994_);
v___x_2996_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___y_2982_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2999_ = l_Lean_Syntax_SepArray_ofElems(v___x_2998_, v___y_2992_);
v___x_3000_ = l_Array_append___redArg(v___y_2983_, v___x_2999_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___y_2982_);
lean_ctor_set(v___x_3001_, 1, v___y_2980_);
lean_ctor_set(v___x_3001_, 2, v___x_3000_);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___y_2982_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_Syntax_node3(v___y_2982_, v___y_2980_, v___x_2997_, v___x_3001_, v___x_3003_);
lean_inc(v___y_2976_);
v___x_3005_ = l_Lean_Syntax_node5(v___y_2982_, v___y_2990_, v___y_2981_, v___y_2976_, v___y_2979_, v___x_2995_, v___x_3004_);
v___y_2840_ = v___y_2974_;
v___y_2841_ = v___y_2986_;
v___y_2842_ = v___y_2975_;
v___y_2843_ = v___y_2976_;
v___y_2844_ = v___y_2988_;
v___y_2845_ = v___y_2992_;
v_stxForExecution_2846_ = v___x_3005_;
v___y_2847_ = v___y_2991_;
v___y_2848_ = v___y_2973_;
v___y_2849_ = v___y_2978_;
v___y_2850_ = v___y_2987_;
v___y_2851_ = v___y_2989_;
v___y_2852_ = v___y_2977_;
v___y_2853_ = v___y_2985_;
v___y_2854_ = v___y_2984_;
goto v___jp_2839_;
}
v___jp_3006_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_inc_ref(v___y_3016_);
v___x_3027_ = l_Array_append___redArg(v___y_3016_, v___y_3026_);
lean_dec_ref(v___y_3026_);
lean_inc(v___y_3013_);
lean_inc(v___y_3015_);
v___x_3028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3028_, 0, v___y_3015_);
lean_ctor_set(v___x_3028_, 1, v___y_3013_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
if (lean_obj_tag(v___y_3009_) == 1)
{
lean_object* v_val_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_val_3029_ = lean_ctor_get(v___y_3009_, 0);
v___x_3030_ = l_Lean_SourceInfo_fromRef(v_val_3029_, v___x_2452_);
v___x_3031_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Array_mkArray1___redArg(v___x_3032_);
v___y_2973_ = v___y_3007_;
v___y_2974_ = v___y_3008_;
v___y_2975_ = v___y_3009_;
v___y_2976_ = v___y_3010_;
v___y_2977_ = v___y_3011_;
v___y_2978_ = v___y_3012_;
v___y_2979_ = v___x_3028_;
v___y_2980_ = v___y_3013_;
v___y_2981_ = v___y_3014_;
v___y_2982_ = v___y_3015_;
v___y_2983_ = v___y_3016_;
v___y_2984_ = v___y_3017_;
v___y_2985_ = v___y_3018_;
v___y_2986_ = v___y_3020_;
v___y_2987_ = v___y_3019_;
v___y_2988_ = v___y_3021_;
v___y_2989_ = v___y_3022_;
v___y_2990_ = v___y_3024_;
v___y_2991_ = v___y_3023_;
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___x_3033_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2973_ = v___y_3007_;
v___y_2974_ = v___y_3008_;
v___y_2975_ = v___y_3009_;
v___y_2976_ = v___y_3010_;
v___y_2977_ = v___y_3011_;
v___y_2978_ = v___y_3012_;
v___y_2979_ = v___x_3028_;
v___y_2980_ = v___y_3013_;
v___y_2981_ = v___y_3014_;
v___y_2982_ = v___y_3015_;
v___y_2983_ = v___y_3016_;
v___y_2984_ = v___y_3017_;
v___y_2985_ = v___y_3018_;
v___y_2986_ = v___y_3020_;
v___y_2987_ = v___y_3019_;
v___y_2988_ = v___y_3021_;
v___y_2989_ = v___y_3022_;
v___y_2990_ = v___y_3024_;
v___y_2991_ = v___y_3023_;
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___x_3034_;
goto v___jp_2972_;
}
}
v___jp_3035_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_inc_ref_n(v___y_3050_, 2);
v___x_3057_ = l_Array_append___redArg(v___y_3050_, v___y_3056_);
lean_dec_ref(v___y_3056_);
lean_inc_n(v___y_3051_, 2);
lean_inc_n(v___y_3045_, 2);
v___x_3058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3058_, 0, v___y_3045_);
lean_ctor_set(v___x_3058_, 1, v___y_3051_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3059_, 0, v___y_3045_);
lean_ctor_set(v___x_3059_, 1, v___y_3051_);
lean_ctor_set(v___x_3059_, 2, v___y_3050_);
lean_inc(v___y_3040_);
v___x_3060_ = l_Lean_Syntax_node5(v___y_3045_, v___y_3039_, v___y_3046_, v___y_3040_, v___y_3055_, v___x_3058_, v___x_3059_);
v___y_2840_ = v___y_3037_;
v___y_2841_ = v___y_3047_;
v___y_2842_ = v___y_3038_;
v___y_2843_ = v___y_3040_;
v___y_2844_ = v___y_3049_;
v___y_2845_ = v___y_3054_;
v_stxForExecution_2846_ = v___x_3060_;
v___y_2847_ = v___y_3053_;
v___y_2848_ = v___y_3036_;
v___y_2849_ = v___y_3042_;
v___y_2850_ = v___y_3048_;
v___y_2851_ = v___y_3052_;
v___y_2852_ = v___y_3041_;
v___y_2853_ = v___y_3044_;
v___y_2854_ = v___y_3043_;
goto v___jp_2839_;
}
v___jp_3061_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc_ref(v___y_3076_);
v___x_3082_ = l_Array_append___redArg(v___y_3076_, v___y_3081_);
lean_dec_ref(v___y_3081_);
lean_inc(v___y_3077_);
lean_inc(v___y_3069_);
v___x_3083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3069_);
lean_ctor_set(v___x_3083_, 1, v___y_3077_);
lean_ctor_set(v___x_3083_, 2, v___x_3082_);
if (lean_obj_tag(v___y_3064_) == 1)
{
lean_object* v_val_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_val_3084_ = lean_ctor_get(v___y_3064_, 0);
v___x_3085_ = l_Lean_SourceInfo_fromRef(v_val_3084_, v___x_2452_);
v___x_3086_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Array_mkArray1___redArg(v___x_3087_);
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3069_;
v___y_3046_ = v___y_3072_;
v___y_3047_ = v___y_3074_;
v___y_3048_ = v___y_3073_;
v___y_3049_ = v___y_3075_;
v___y_3050_ = v___y_3076_;
v___y_3051_ = v___y_3077_;
v___y_3052_ = v___y_3078_;
v___y_3053_ = v___y_3079_;
v___y_3054_ = v___y_3080_;
v___y_3055_ = v___x_3083_;
v___y_3056_ = v___x_3088_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3069_;
v___y_3046_ = v___y_3072_;
v___y_3047_ = v___y_3074_;
v___y_3048_ = v___y_3073_;
v___y_3049_ = v___y_3075_;
v___y_3050_ = v___y_3076_;
v___y_3051_ = v___y_3077_;
v___y_3052_ = v___y_3078_;
v___y_3053_ = v___y_3079_;
v___y_3054_ = v___y_3080_;
v___y_3055_ = v___x_3083_;
v___y_3056_ = v___x_3089_;
goto v___jp_3035_;
}
}
v___jp_3090_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_inc_ref_n(v___y_3093_, 2);
v___x_3112_ = l_Array_append___redArg(v___y_3093_, v___y_3111_);
lean_dec_ref(v___y_3111_);
lean_inc_n(v___y_3098_, 2);
lean_inc_n(v___y_3109_, 2);
v___x_3113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3113_, 0, v___y_3109_);
lean_ctor_set(v___x_3113_, 1, v___y_3098_);
lean_ctor_set(v___x_3113_, 2, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3114_, 0, v___y_3109_);
lean_ctor_set(v___x_3114_, 1, v___y_3098_);
lean_ctor_set(v___x_3114_, 2, v___y_3093_);
lean_inc(v___y_3095_);
v___x_3115_ = l_Lean_Syntax_node5(v___y_3109_, v___y_3099_, v___y_3104_, v___y_3095_, v___y_3110_, v___x_3113_, v___x_3114_);
v___y_2840_ = v___y_3092_;
v___y_2841_ = v___y_3102_;
v___y_2842_ = v___y_3094_;
v___y_2843_ = v___y_3095_;
v___y_2844_ = v___y_3105_;
v___y_2845_ = v___y_3108_;
v_stxForExecution_2846_ = v___x_3115_;
v___y_2847_ = v___y_3107_;
v___y_2848_ = v___y_3091_;
v___y_2849_ = v___y_3097_;
v___y_2850_ = v___y_3103_;
v___y_2851_ = v___y_3106_;
v___y_2852_ = v___y_3096_;
v___y_2853_ = v___y_3101_;
v___y_2854_ = v___y_3100_;
goto v___jp_2839_;
}
v___jp_3116_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_inc_ref(v___y_3118_);
v___x_3137_ = l_Array_append___redArg(v___y_3118_, v___y_3136_);
lean_dec_ref(v___y_3136_);
lean_inc(v___y_3124_);
lean_inc(v___y_3135_);
v___x_3138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3138_, 0, v___y_3135_);
lean_ctor_set(v___x_3138_, 1, v___y_3124_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
if (lean_obj_tag(v___y_3120_) == 1)
{
lean_object* v_val_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_val_3139_ = lean_ctor_get(v___y_3120_, 0);
v___x_3140_ = l_Lean_SourceInfo_fromRef(v_val_3139_, v___x_2452_);
v___x_3141_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l_Array_mkArray1___redArg(v___x_3142_);
v___y_3091_ = v___y_3117_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3118_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
v___y_3101_ = v___y_3127_;
v___y_3102_ = v___y_3129_;
v___y_3103_ = v___y_3128_;
v___y_3104_ = v___y_3130_;
v___y_3105_ = v___y_3131_;
v___y_3106_ = v___y_3132_;
v___y_3107_ = v___y_3133_;
v___y_3108_ = v___y_3134_;
v___y_3109_ = v___y_3135_;
v___y_3110_ = v___x_3138_;
v___y_3111_ = v___x_3143_;
goto v___jp_3090_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3091_ = v___y_3117_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3118_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
v___y_3101_ = v___y_3127_;
v___y_3102_ = v___y_3129_;
v___y_3103_ = v___y_3128_;
v___y_3104_ = v___y_3130_;
v___y_3105_ = v___y_3131_;
v___y_3106_ = v___y_3132_;
v___y_3107_ = v___y_3133_;
v___y_3108_ = v___y_3134_;
v___y_3109_ = v___y_3135_;
v___y_3110_ = v___x_3138_;
v___y_3111_ = v___x_3144_;
goto v___jp_3090_;
}
}
v___jp_3145_:
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = lean_array_get_size(v_argsArray_3151_);
v___x_3161_ = lean_nat_dec_eq(v___x_3160_, v___x_2467_);
if (v___x_3161_ == 0)
{
if (lean_obj_tag(v___y_3146_) == 0)
{
lean_object* v_ref_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_ref_3162_ = lean_ctor_get(v___y_3158_, 2);
v___x_3163_ = l_Lean_SourceInfo_fromRef(v_ref_3162_, v___x_3161_);
v___x_3164_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3165_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3164_);
v___x_3166_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_3167_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3170_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3150_) == 1)
{
lean_object* v_val_3171_; lean_object* v___x_3172_; 
v_val_3171_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_val_3171_);
v___x_3172_ = l_Array_mkArray1___redArg(v_val_3171_);
v___y_2944_ = v___y_3153_;
v___y_2945_ = v___y_3146_;
v___y_2946_ = v___x_3165_;
v___y_2947_ = v___y_3149_;
v___y_2948_ = v___y_3148_;
v___y_2949_ = v___y_3157_;
v___y_2950_ = v___y_3154_;
v___y_2951_ = v___y_3159_;
v___y_2952_ = v___y_3158_;
v___y_2953_ = v___y_3155_;
v___y_2954_ = v___y_3147_;
v___y_2955_ = v___y_3150_;
v___y_2956_ = v___x_3170_;
v___y_2957_ = v___y_3156_;
v___y_2958_ = v___x_3168_;
v___y_2959_ = v___x_3163_;
v___y_2960_ = v___y_3152_;
v___y_2961_ = v___x_3169_;
v___y_2962_ = v_argsArray_3151_;
v___y_2963_ = v___x_3172_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3173_; 
v___x_3173_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2944_ = v___y_3153_;
v___y_2945_ = v___y_3146_;
v___y_2946_ = v___x_3165_;
v___y_2947_ = v___y_3149_;
v___y_2948_ = v___y_3148_;
v___y_2949_ = v___y_3157_;
v___y_2950_ = v___y_3154_;
v___y_2951_ = v___y_3159_;
v___y_2952_ = v___y_3158_;
v___y_2953_ = v___y_3155_;
v___y_2954_ = v___y_3147_;
v___y_2955_ = v___y_3150_;
v___y_2956_ = v___x_3170_;
v___y_2957_ = v___y_3156_;
v___y_2958_ = v___x_3168_;
v___y_2959_ = v___x_3163_;
v___y_2960_ = v___y_3152_;
v___y_2961_ = v___x_3169_;
v___y_2962_ = v_argsArray_3151_;
v___y_2963_ = v___x_3173_;
goto v___jp_2943_;
}
}
else
{
lean_object* v_ref_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_ref_3174_ = lean_ctor_get(v___y_3158_, 2);
v___x_3175_ = l_Lean_SourceInfo_fromRef(v_ref_3174_, v___x_3161_);
v___x_3176_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3177_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3176_);
v___x_3178_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_3179_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3182_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3150_) == 1)
{
lean_object* v_val_3183_; lean_object* v___x_3184_; 
v_val_3183_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_val_3183_);
v___x_3184_ = l_Array_mkArray1___redArg(v_val_3183_);
v___y_3007_ = v___y_3153_;
v___y_3008_ = v___y_3146_;
v___y_3009_ = v___y_3149_;
v___y_3010_ = v___y_3148_;
v___y_3011_ = v___y_3157_;
v___y_3012_ = v___y_3154_;
v___y_3013_ = v___x_3181_;
v___y_3014_ = v___x_3180_;
v___y_3015_ = v___x_3175_;
v___y_3016_ = v___x_3182_;
v___y_3017_ = v___y_3159_;
v___y_3018_ = v___y_3158_;
v___y_3019_ = v___y_3155_;
v___y_3020_ = v___y_3147_;
v___y_3021_ = v___y_3150_;
v___y_3022_ = v___y_3156_;
v___y_3023_ = v___y_3152_;
v___y_3024_ = v___x_3177_;
v___y_3025_ = v_argsArray_3151_;
v___y_3026_ = v___x_3184_;
goto v___jp_3006_;
}
else
{
lean_object* v___x_3185_; 
v___x_3185_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3007_ = v___y_3153_;
v___y_3008_ = v___y_3146_;
v___y_3009_ = v___y_3149_;
v___y_3010_ = v___y_3148_;
v___y_3011_ = v___y_3157_;
v___y_3012_ = v___y_3154_;
v___y_3013_ = v___x_3181_;
v___y_3014_ = v___x_3180_;
v___y_3015_ = v___x_3175_;
v___y_3016_ = v___x_3182_;
v___y_3017_ = v___y_3159_;
v___y_3018_ = v___y_3158_;
v___y_3019_ = v___y_3155_;
v___y_3020_ = v___y_3147_;
v___y_3021_ = v___y_3150_;
v___y_3022_ = v___y_3156_;
v___y_3023_ = v___y_3152_;
v___y_3024_ = v___x_3177_;
v___y_3025_ = v_argsArray_3151_;
v___y_3026_ = v___x_3185_;
goto v___jp_3006_;
}
}
}
else
{
if (lean_obj_tag(v___y_3146_) == 0)
{
lean_object* v_ref_3186_; uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_ref_3186_ = lean_ctor_get(v___y_3158_, 2);
v___x_3187_ = 0;
v___x_3188_ = l_Lean_SourceInfo_fromRef(v_ref_3186_, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3190_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3189_);
v___x_3191_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_3192_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3195_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3150_) == 1)
{
lean_object* v_val_3196_; lean_object* v___x_3197_; 
v_val_3196_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_val_3196_);
v___x_3197_ = l_Array_mkArray1___redArg(v_val_3196_);
v___y_3062_ = v___y_3153_;
v___y_3063_ = v___y_3146_;
v___y_3064_ = v___y_3149_;
v___y_3065_ = v___x_3190_;
v___y_3066_ = v___y_3148_;
v___y_3067_ = v___y_3157_;
v___y_3068_ = v___y_3154_;
v___y_3069_ = v___x_3188_;
v___y_3070_ = v___y_3159_;
v___y_3071_ = v___y_3158_;
v___y_3072_ = v___x_3193_;
v___y_3073_ = v___y_3155_;
v___y_3074_ = v___y_3147_;
v___y_3075_ = v___y_3150_;
v___y_3076_ = v___x_3195_;
v___y_3077_ = v___x_3194_;
v___y_3078_ = v___y_3156_;
v___y_3079_ = v___y_3152_;
v___y_3080_ = v_argsArray_3151_;
v___y_3081_ = v___x_3197_;
goto v___jp_3061_;
}
else
{
lean_object* v___x_3198_; 
v___x_3198_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3062_ = v___y_3153_;
v___y_3063_ = v___y_3146_;
v___y_3064_ = v___y_3149_;
v___y_3065_ = v___x_3190_;
v___y_3066_ = v___y_3148_;
v___y_3067_ = v___y_3157_;
v___y_3068_ = v___y_3154_;
v___y_3069_ = v___x_3188_;
v___y_3070_ = v___y_3159_;
v___y_3071_ = v___y_3158_;
v___y_3072_ = v___x_3193_;
v___y_3073_ = v___y_3155_;
v___y_3074_ = v___y_3147_;
v___y_3075_ = v___y_3150_;
v___y_3076_ = v___x_3195_;
v___y_3077_ = v___x_3194_;
v___y_3078_ = v___y_3156_;
v___y_3079_ = v___y_3152_;
v___y_3080_ = v_argsArray_3151_;
v___y_3081_ = v___x_3198_;
goto v___jp_3061_;
}
}
else
{
lean_object* v_ref_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_ref_3199_ = lean_ctor_get(v___y_3158_, 2);
v___x_3200_ = 0;
v___x_3201_ = l_Lean_SourceInfo_fromRef(v_ref_3199_, v___x_3200_);
v___x_3202_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3203_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3202_);
v___x_3204_ = l_Lean_SourceInfo_fromRef(v_tk_2468_, v___x_2452_);
v___x_3205_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3208_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3150_) == 1)
{
lean_object* v_val_3209_; lean_object* v___x_3210_; 
v_val_3209_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_val_3209_);
v___x_3210_ = l_Array_mkArray1___redArg(v_val_3209_);
v___y_3117_ = v___y_3153_;
v___y_3118_ = v___x_3208_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3149_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___y_3157_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___x_3207_;
v___y_3125_ = v___x_3203_;
v___y_3126_ = v___y_3159_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3147_;
v___y_3130_ = v___x_3206_;
v___y_3131_ = v___y_3150_;
v___y_3132_ = v___y_3156_;
v___y_3133_ = v___y_3152_;
v___y_3134_ = v_argsArray_3151_;
v___y_3135_ = v___x_3201_;
v___y_3136_ = v___x_3210_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3211_; 
v___x_3211_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3117_ = v___y_3153_;
v___y_3118_ = v___x_3208_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3149_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___y_3157_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___x_3207_;
v___y_3125_ = v___x_3203_;
v___y_3126_ = v___y_3159_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3147_;
v___y_3130_ = v___x_3206_;
v___y_3131_ = v___y_3150_;
v___y_3132_ = v___y_3156_;
v___y_3133_ = v___y_3152_;
v___y_3134_ = v_argsArray_3151_;
v___y_3135_ = v___x_3201_;
v___y_3136_ = v___x_3211_;
goto v___jp_3116_;
}
}
}
}
v___jp_3212_:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3215_, v___y_3219_, v___y_3225_, v___y_3213_, v___y_3221_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_LibrarySuggestions_select(v_a_3229_, v___y_3227_, v___y_3219_, v___y_3225_, v___y_3213_, v___y_3221_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; size_t v_sz_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_sz_3232_ = lean_array_size(v_a_3231_);
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3231_, v_sz_3232_, v___x_3233_, v___y_3226_, v___y_3216_, v___y_3215_, v___y_3217_, v___y_3222_, v___y_3219_, v___y_3225_, v___y_3213_, v___y_3221_);
lean_dec(v_a_3231_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___y_3146_ = v___y_3214_;
v___y_3147_ = v___y_3223_;
v___y_3148_ = v___y_3220_;
v___y_3149_ = v___y_3218_;
v___y_3150_ = v___y_3224_;
v_argsArray_3151_ = v_a_3235_;
v___y_3152_ = v___y_3216_;
v___y_3153_ = v___y_3215_;
v___y_3154_ = v___y_3217_;
v___y_3155_ = v___y_3222_;
v___y_3156_ = v___y_3219_;
v___y_3157_ = v___y_3225_;
v___y_3158_ = v___y_3213_;
v___y_3159_ = v___y_3221_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v___y_3224_);
lean_dec(v___y_3220_);
lean_dec(v___y_3218_);
lean_dec(v___y_3214_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v_a_3236_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3234_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3234_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3224_);
lean_dec(v___y_3220_);
lean_dec(v___y_3218_);
lean_dec(v___y_3214_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v_a_3244_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3230_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3230_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3224_);
lean_dec(v___y_3220_);
lean_dec(v___y_3218_);
lean_dec(v___y_3214_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v_a_3252_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3228_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3228_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
v___jp_3260_:
{
lean_object* v_config_3276_; uint8_t v_suggestions_3277_; 
v_config_3276_ = lean_ctor_get(v___y_3269_, 0);
lean_inc_ref(v_config_3276_);
lean_dec_ref(v___y_3269_);
v_suggestions_3277_ = lean_ctor_get_uint8(v_config_3276_, sizeof(void*)*3 + 26);
if (v_suggestions_3277_ == 0)
{
lean_dec_ref(v_config_3276_);
lean_dec_ref(v___f_2456_);
v___y_3146_ = v___y_3262_;
v___y_3147_ = v___y_3272_;
v___y_3148_ = v___y_3268_;
v___y_3149_ = v___y_3266_;
v___y_3150_ = v___y_3273_;
v_argsArray_3151_ = v___y_3275_;
v___y_3152_ = v___y_3264_;
v___y_3153_ = v___y_3263_;
v___y_3154_ = v___y_3265_;
v___y_3155_ = v___y_3271_;
v___y_3156_ = v___y_3267_;
v___y_3157_ = v___y_3274_;
v___y_3158_ = v___y_3261_;
v___y_3159_ = v___y_3270_;
goto v___jp_3145_;
}
else
{
lean_object* v_maxSuggestions_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_maxSuggestions_3278_ = lean_ctor_get(v_config_3276_, 2);
lean_inc(v_maxSuggestions_3278_);
lean_dec_ref(v_config_3276_);
v___x_3279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3280_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3278_) == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = lean_unsigned_to_nat(100u);
v___x_3282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3279_);
lean_ctor_set(v___x_3282_, 2, v___f_2456_);
lean_ctor_set(v___x_3282_, 3, v___x_3280_);
v___y_3213_ = v___y_3261_;
v___y_3214_ = v___y_3262_;
v___y_3215_ = v___y_3263_;
v___y_3216_ = v___y_3264_;
v___y_3217_ = v___y_3265_;
v___y_3218_ = v___y_3266_;
v___y_3219_ = v___y_3267_;
v___y_3220_ = v___y_3268_;
v___y_3221_ = v___y_3270_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___y_3272_;
v___y_3224_ = v___y_3273_;
v___y_3225_ = v___y_3274_;
v___y_3226_ = v___y_3275_;
v___y_3227_ = v___x_3282_;
goto v___jp_3212_;
}
else
{
lean_object* v_val_3283_; lean_object* v___x_3284_; 
v_val_3283_ = lean_ctor_get(v_maxSuggestions_3278_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v_maxSuggestions_3278_, 1);
v___x_3284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3284_, 0, v_val_3283_);
lean_ctor_set(v___x_3284_, 1, v___x_3279_);
lean_ctor_set(v___x_3284_, 2, v___f_2456_);
lean_ctor_set(v___x_3284_, 3, v___x_3280_);
v___y_3213_ = v___y_3261_;
v___y_3214_ = v___y_3262_;
v___y_3215_ = v___y_3263_;
v___y_3216_ = v___y_3264_;
v___y_3217_ = v___y_3265_;
v___y_3218_ = v___y_3266_;
v___y_3219_ = v___y_3267_;
v___y_3220_ = v___y_3268_;
v___y_3221_ = v___y_3270_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___y_3272_;
v___y_3224_ = v___y_3273_;
v___y_3225_ = v___y_3274_;
v___y_3226_ = v___y_3275_;
v___y_3227_ = v___x_3284_;
goto v___jp_3212_;
}
}
}
v___jp_3285_:
{
uint8_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = 1;
lean_inc(v___y_3291_);
v___x_3300_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3291_, v___x_3299_, v___y_3288_, v___y_3286_, v___y_3295_);
if (lean_obj_tag(v___x_3300_) == 0)
{
if (lean_obj_tag(v___y_3294_) == 1)
{
lean_object* v_a_3301_; lean_object* v_val_3302_; lean_object* v___x_3303_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v_val_3302_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___y_3294_, 1);
v___x_3303_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3302_);
lean_dec(v_val_3302_);
v___y_3261_ = v___y_3286_;
v___y_3262_ = v___y_3287_;
v___y_3263_ = v___y_3289_;
v___y_3264_ = v___y_3288_;
v___y_3265_ = v___y_3290_;
v___y_3266_ = v___y_3292_;
v___y_3267_ = v___y_3293_;
v___y_3268_ = v___y_3291_;
v___y_3269_ = v_a_3301_;
v___y_3270_ = v___y_3295_;
v___y_3271_ = v___y_3296_;
v___y_3272_ = v___x_3299_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v___y_3297_;
v___y_3275_ = v___x_3303_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
lean_dec(v___y_3294_);
v_a_3304_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3300_, 1);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3261_ = v___y_3286_;
v___y_3262_ = v___y_3287_;
v___y_3263_ = v___y_3289_;
v___y_3264_ = v___y_3288_;
v___y_3265_ = v___y_3290_;
v___y_3266_ = v___y_3292_;
v___y_3267_ = v___y_3293_;
v___y_3268_ = v___y_3291_;
v___y_3269_ = v_a_3304_;
v___y_3270_ = v___y_3295_;
v___y_3271_ = v___y_3296_;
v___y_3272_ = v___x_3299_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v___y_3297_;
v___y_3275_ = v___x_3305_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v___y_3298_);
lean_dec(v___y_3294_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v___y_3287_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v_a_3306_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3300_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3300_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Syntax_getOptional_x3f(v___y_3318_);
lean_dec(v___y_3318_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_box(0);
v___y_3286_ = v___y_3326_;
v___y_3287_ = v___y_3315_;
v___y_3288_ = v___y_3320_;
v___y_3289_ = v___y_3321_;
v___y_3290_ = v___y_3322_;
v___y_3291_ = v___y_3317_;
v___y_3292_ = v___y_3316_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v_args_3319_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___y_3323_;
v___y_3297_ = v___y_3325_;
v___y_3298_ = v___x_3329_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_val_3330_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3328_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_val_3330_);
lean_dec(v___x_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_val_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
v___y_3286_ = v___y_3326_;
v___y_3287_ = v___y_3315_;
v___y_3288_ = v___y_3320_;
v___y_3289_ = v___y_3321_;
v___y_3290_ = v___y_3322_;
v___y_3291_ = v___y_3317_;
v___y_3292_ = v___y_3316_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v_args_3319_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___y_3323_;
v___y_3297_ = v___y_3325_;
v___y_3298_ = v___x_3335_;
goto v___jp_3285_;
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3353_ = lean_unsigned_to_nat(3u);
v___x_3354_ = l_Lean_Syntax_getArg(v___y_3341_, v___x_3353_);
lean_dec(v___y_3341_);
v___x_3355_ = l_Lean_Syntax_isNone(v___x_3354_);
if (v___x_3355_ == 0)
{
uint8_t v___x_3356_; 
lean_inc(v___x_3354_);
v___x_3356_ = l_Lean_Syntax_matchesNull(v___x_3354_, v___x_3338_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
lean_dec(v___x_3354_);
lean_dec(v_o_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3340_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3358_ = l_Lean_Syntax_getArg(v___x_3354_, v___x_2467_);
lean_dec(v___x_3354_);
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3360_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3359_);
lean_inc(v___x_3358_);
v___x_3361_ = l_Lean_Syntax_isOfKind(v___x_3358_, v___x_3360_);
lean_dec(v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec(v___x_3358_);
lean_dec(v_o_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3340_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; lean_object* v_args_3364_; lean_object* v___x_3365_; 
v___x_3363_ = l_Lean_Syntax_getArg(v___x_3358_, v___x_3338_);
lean_dec(v___x_3358_);
v_args_3364_ = l_Lean_Syntax_getArgs(v___x_3363_);
lean_dec(v___x_3363_);
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_args_3364_);
v___y_3315_ = v___y_3340_;
v___y_3316_ = v_o_3344_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3343_;
v_args_3319_ = v___x_3365_;
v___y_3320_ = v___y_3345_;
v___y_3321_ = v___y_3346_;
v___y_3322_ = v___y_3347_;
v___y_3323_ = v___y_3348_;
v___y_3324_ = v___y_3349_;
v___y_3325_ = v___y_3350_;
v___y_3326_ = v___y_3351_;
v___y_3327_ = v___y_3352_;
goto v___jp_3314_;
}
}
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3354_);
v___x_3366_ = lean_box(0);
v___y_3315_ = v___y_3340_;
v___y_3316_ = v_o_3344_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3343_;
v_args_3319_ = v___x_3366_;
v___y_3320_ = v___y_3345_;
v___y_3321_ = v___y_3346_;
v___y_3322_ = v___y_3347_;
v___y_3323_ = v___y_3348_;
v___y_3324_ = v___y_3349_;
v___y_3325_ = v___y_3350_;
v___y_3326_ = v___y_3351_;
v___y_3327_ = v___y_3352_;
goto v___jp_3314_;
}
}
v___jp_3367_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3377_ = lean_unsigned_to_nat(2u);
v___x_3378_ = l_Lean_Syntax_getArg(v_stx_2451_, v___x_3377_);
v___x_3379_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3380_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3379_);
lean_inc(v___x_3378_);
v___x_3381_ = l_Lean_Syntax_isOfKind(v___x_3378_, v___x_3380_);
lean_dec(v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_dec(v___x_3378_);
lean_dec(v_bang_3368_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3382_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3382_;
}
else
{
lean_object* v_cfg_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_cfg_3383_ = l_Lean_Syntax_getArg(v___x_3378_, v___x_2467_);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2455_);
lean_inc_ref(v___x_2454_);
lean_inc_ref(v___x_2453_);
v___x_3385_ = l_Lean_Name_mkStr4(v___x_2453_, v___x_2454_, v___x_2455_, v___x_3384_);
lean_inc(v_cfg_3383_);
v___x_3386_ = l_Lean_Syntax_isOfKind(v_cfg_3383_, v___x_3385_);
lean_dec(v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec(v_cfg_3383_);
lean_dec(v___x_3378_);
lean_dec(v_bang_3368_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = l_Lean_Syntax_getArg(v___x_3378_, v___x_3338_);
v___x_3389_ = l_Lean_Syntax_getArg(v___x_3378_, v___x_3377_);
v___x_3390_ = l_Lean_Syntax_isNone(v___x_3389_);
if (v___x_3390_ == 0)
{
uint8_t v___x_3391_; 
lean_inc(v___x_3389_);
v___x_3391_ = l_Lean_Syntax_matchesNull(v___x_3389_, v___x_3338_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_dec(v___x_3389_);
lean_dec(v___x_3388_);
lean_dec(v_cfg_3383_);
lean_dec(v___x_3378_);
lean_dec(v_bang_3368_);
lean_dec(v_tk_2468_);
lean_dec_ref(v___f_2456_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_3392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3392_;
}
else
{
lean_object* v_o_3393_; lean_object* v___x_3394_; 
v_o_3393_ = l_Lean_Syntax_getArg(v___x_3389_, v___x_2467_);
lean_dec(v___x_3389_);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_o_3393_);
v___y_3340_ = v_bang_3368_;
v___y_3341_ = v___x_3378_;
v___y_3342_ = v_cfg_3383_;
v___y_3343_ = v___x_3388_;
v_o_3344_ = v___x_3394_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3370_;
v___y_3347_ = v___y_3371_;
v___y_3348_ = v___y_3372_;
v___y_3349_ = v___y_3373_;
v___y_3350_ = v___y_3374_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
goto v___jp_3339_;
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v___x_3389_);
v___x_3395_ = lean_box(0);
v___y_3340_ = v_bang_3368_;
v___y_3341_ = v___x_3378_;
v___y_3342_ = v_cfg_3383_;
v___y_3343_ = v___x_3388_;
v_o_3344_ = v___x_3395_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3370_;
v___y_3347_ = v___y_3371_;
v___y_3348_ = v___y_3372_;
v___y_3349_ = v___y_3373_;
v___y_3350_ = v___y_3374_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
goto v___jp_3339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3403_, lean_object* v_stx_3404_, lean_object* v___x_3405_, lean_object* v___x_3406_, lean_object* v___x_3407_, lean_object* v___x_3408_, lean_object* v___f_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_30635__boxed_3419_; uint8_t v___x_30636__boxed_3420_; lean_object* v_res_3421_; 
v___x_30635__boxed_3419_ = lean_unbox(v___x_3403_);
v___x_30636__boxed_3420_ = lean_unbox(v___x_3405_);
v_res_3421_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_30635__boxed_3419_, v_stx_3404_, v___x_30636__boxed_3420_, v___x_3406_, v___x_3407_, v___x_3408_, v___f_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_stx_3404_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; uint8_t v___x_3443_; lean_object* v___f_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___y_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3441_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3428_);
v___x_3442_ = l_Lean_Syntax_isOfKind(v_stx_3428_, v___x_3441_);
v___x_3443_ = 1;
v___f_3444_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3445_ = lean_box(v___x_3442_);
v___x_3446_ = lean_box(v___x_3443_);
v___y_3447_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3447_, 0, v___x_3445_);
lean_closure_set(v___y_3447_, 1, v_stx_3428_);
lean_closure_set(v___y_3447_, 2, v___x_3446_);
lean_closure_set(v___y_3447_, 3, v___x_3438_);
lean_closure_set(v___y_3447_, 4, v___x_3439_);
lean_closure_set(v___y_3447_, 5, v___x_3440_);
lean_closure_set(v___y_3447_, 6, v___f_3444_);
v___x_3448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3448_, 0, v___y_3447_);
v___x_3449_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3448_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3461_, lean_object* v_as_3462_, lean_object* v_as_x27_3463_, lean_object* v_b_3464_, lean_object* v_a_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3461_, v_as_x27_3463_, v_b_3464_, v___y_3472_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3476_, lean_object* v_as_3477_, lean_object* v_as_x27_3478_, lean_object* v_b_3479_, lean_object* v_a_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3476_, v_as_3477_, v_as_x27_3478_, v_b_3479_, v_a_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_as_x27_3478_);
lean_dec(v_as_3477_);
lean_dec(v___x_3476_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3498_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3501_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3502_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3498_, v___x_3499_, v___x_3500_, v___x_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3532_ = l_Lean_addBuiltinDeclarationRanges(v___x_3530_, v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3535_, lean_object* v_simprocs_3536_, lean_object* v_fvarIdsToSimp_3537_, uint8_t v_simplifyTarget_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = lean_unsigned_to_nat(32u);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3547_);
lean_dec_ref(v___x_3548_);
v___x_3549_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3550_ = l_Lean_Meta_dsimpGoal(v_a_3546_, v_ctx_3535_, v_simprocs_3536_, v_simplifyTarget_3538_, v_fvarIdsToSimp_3537_, v___x_3549_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v_fst_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_fst_3552_ = lean_ctor_get(v_a_3551_, 0);
if (lean_obj_tag(v_fst_3552_) == 0)
{
lean_object* v_snd_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_snd_3553_ = lean_ctor_get(v_a_3551_, 1);
lean_inc(v_snd_3553_);
lean_dec(v_a_3551_);
v___x_3554_ = lean_box(0);
v___x_3555_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3554_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v___x_3555_, 0);
lean_dec(v_unused_3563_);
v___x_3557_ = v___x_3555_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_dec(v___x_3555_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v_snd_3553_);
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_snd_3553_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_snd_3553_);
v_a_3564_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3555_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3555_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v_snd_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3598_; 
lean_inc_ref(v_fst_3552_);
v_snd_3572_ = lean_ctor_get(v_a_3551_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v_a_3551_, 0);
lean_dec(v_unused_3599_);
v___x_3574_ = v_a_3551_;
v_isShared_3575_ = v_isSharedCheck_3598_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_snd_3572_);
lean_dec(v_a_3551_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3598_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_val_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v_val_3576_ = lean_ctor_get(v_fst_3552_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v_fst_3552_, 1);
v___x_3577_ = lean_box(0);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 1);
lean_ctor_set(v___x_3574_, 1, v___x_3577_);
lean_ctor_set(v___x_3574_, 0, v_val_3576_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_val_3576_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3579_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v___x_3580_, 0);
lean_dec(v_unused_3588_);
v___x_3582_ = v___x_3580_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_dec(v___x_3580_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v_snd_3572_);
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_snd_3572_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec(v_snd_3572_);
v_a_3589_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3580_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3580_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
v_a_3600_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3550_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3550_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v_fvarIdsToSimp_3537_);
lean_dec_ref(v_simprocs_3536_);
lean_dec_ref(v_ctx_3535_);
v_a_3608_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3545_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3545_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3616_, lean_object* v_simprocs_3617_, lean_object* v_fvarIdsToSimp_3618_, lean_object* v_simplifyTarget_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
uint8_t v_simplifyTarget_boxed_3626_; lean_object* v_res_3627_; 
v_simplifyTarget_boxed_3626_ = lean_unbox(v_simplifyTarget_3619_);
v_res_3627_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3616_, v_simprocs_3617_, v_fvarIdsToSimp_3618_, v_simplifyTarget_boxed_3626_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3628_, lean_object* v_simprocs_3629_, lean_object* v_fvarIdsToSimp_3630_, uint8_t v_simplifyTarget_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3628_, v_simprocs_3629_, v_fvarIdsToSimp_3630_, v_simplifyTarget_3631_, v_a_3633_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3642_, lean_object* v_simprocs_3643_, lean_object* v_fvarIdsToSimp_3644_, lean_object* v_simplifyTarget_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
uint8_t v_simplifyTarget_boxed_3655_; lean_object* v_res_3656_; 
v_simplifyTarget_boxed_3655_ = lean_unbox(v_simplifyTarget_3645_);
v_res_3656_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3642_, v_simprocs_3643_, v_fvarIdsToSimp_3644_, v_simplifyTarget_boxed_3655_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3657_, lean_object* v_simprocs_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3660_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v___x_3670_ = l_Lean_MVarId_getNondepPropHyps(v_a_3669_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v___x_3672_ = 1;
v___x_3673_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3657_, v_simprocs_3658_, v_a_3671_, v___x_3672_, v___y_3660_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3673_;
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_simprocs_3658_);
lean_dec_ref(v_ctx_3657_);
v_a_3674_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3670_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3670_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v_simprocs_3658_);
lean_dec_ref(v_ctx_3657_);
v_a_3682_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3668_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3668_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3690_, lean_object* v_simprocs_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3690_, v_simprocs_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3702_, lean_object* v_ctx_3703_, lean_object* v_simprocs_3704_, uint8_t v_type_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3702_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3703_, v_simprocs_3704_, v_a_3716_, v_type_3705_, v___y_3707_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3717_;
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_simprocs_3704_);
lean_dec_ref(v_ctx_3703_);
v_a_3718_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3715_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3715_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3726_, lean_object* v_ctx_3727_, lean_object* v_simprocs_3728_, lean_object* v_type_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
uint8_t v_type_555__boxed_3739_; lean_object* v_res_3740_; 
v_type_555__boxed_3739_ = lean_unbox(v_type_3729_);
v_res_3740_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3726_, v_ctx_3727_, v_simprocs_3728_, v_type_555__boxed_3739_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3741_, lean_object* v_simprocs_3742_, lean_object* v_loc_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
if (lean_obj_tag(v_loc_3743_) == 0)
{
lean_object* v___f_3753_; lean_object* v___x_3754_; 
v___f_3753_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3753_, 0, v_ctx_3741_);
lean_closure_set(v___f_3753_, 1, v_simprocs_3742_);
v___x_3754_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3753_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3754_;
}
else
{
lean_object* v_hypotheses_3755_; uint8_t v_type_3756_; lean_object* v___x_3757_; lean_object* v___f_3758_; lean_object* v___x_3759_; 
v_hypotheses_3755_ = lean_ctor_get(v_loc_3743_, 0);
lean_inc_ref(v_hypotheses_3755_);
v_type_3756_ = lean_ctor_get_uint8(v_loc_3743_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3743_, 1);
v___x_3757_ = lean_box(v_type_3756_);
v___f_3758_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3758_, 0, v_hypotheses_3755_);
lean_closure_set(v___f_3758_, 1, v_ctx_3741_);
lean_closure_set(v___f_3758_, 2, v_simprocs_3742_);
lean_closure_set(v___f_3758_, 3, v___x_3757_);
v___x_3759_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3758_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3760_, lean_object* v_simprocs_3761_, lean_object* v_loc_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3760_, v_simprocs_3761_, v_loc_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3777_, lean_object* v_stx_3778_, uint8_t v___x_3779_, lean_object* v___x_3780_, lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
if (v___x_3777_ == 0)
{
lean_object* v___x_3792_; 
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_3792_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; lean_object* v_tk_3794_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v_stx_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v_args_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___x_4148_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v_o_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v_bang_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_3793_ = lean_unsigned_to_nat(0u);
v_tk_3794_ = l_Lean_Syntax_getArg(v_stx_3778_, v___x_3793_);
v___x_4148_ = lean_unsigned_to_nat(1u);
v___x_4204_ = l_Lean_Syntax_getArg(v_stx_3778_, v___x_4148_);
v___x_4205_ = l_Lean_Syntax_isNone(v___x_4204_);
if (v___x_4205_ == 0)
{
uint8_t v___x_4206_; 
lean_inc(v___x_4204_);
v___x_4206_ = l_Lean_Syntax_matchesNull(v___x_4204_, v___x_4148_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; 
lean_dec(v___x_4204_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4207_;
}
else
{
lean_object* v_bang_4208_; lean_object* v___x_4209_; 
v_bang_4208_ = l_Lean_Syntax_getArg(v___x_4204_, v___x_3793_);
lean_dec(v___x_4204_);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_bang_4208_);
v_bang_4177_ = v___x_4209_;
v___y_4178_ = v___y_3783_;
v___y_4179_ = v___y_3784_;
v___y_4180_ = v___y_3785_;
v___y_4181_ = v___y_3786_;
v___y_4182_ = v___y_3787_;
v___y_4183_ = v___y_3788_;
v___y_4184_ = v___y_3789_;
v___y_4185_ = v___y_3790_;
goto v___jp_4176_;
}
}
else
{
lean_object* v___x_4210_; 
lean_dec(v___x_4204_);
v___x_4210_ = lean_box(0);
v_bang_4177_ = v___x_4210_;
v___y_4178_ = v___y_3783_;
v___y_4179_ = v___y_3784_;
v___y_4180_ = v___y_3785_;
v___y_4181_ = v___y_3786_;
v___y_4182_ = v___y_3787_;
v___y_4183_ = v___y_3788_;
v___y_4184_ = v___y_3789_;
v___y_4185_ = v___y_3790_;
goto v___jp_4176_;
}
v___jp_3795_:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3802_, v___y_3804_, v___y_3807_, v___y_3806_, v___y_3797_, v___y_3798_, v___y_3805_, v___y_3801_, v___y_3803_, v___y_3800_, v___y_3796_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v_usedTheorems_3810_; lean_object* v_diag_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3853_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v_usedTheorems_3810_ = lean_ctor_get(v_a_3809_, 0);
v_diag_3811_ = lean_ctor_get(v_a_3809_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_a_3809_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3813_ = v_a_3809_;
v_isShared_3814_ = v_isSharedCheck_3853_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_diag_3811_);
lean_inc(v_usedTheorems_3810_);
lean_dec(v_a_3809_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3853_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3799_, v_usedTheorems_3810_, v___y_3801_, v___y_3803_, v___y_3800_, v___y_3796_);
lean_dec_ref(v_usedTheorems_3810_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v_ref_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v_ref_3817_ = lean_ctor_get(v___y_3800_, 2);
v___x_3818_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 1, v_a_3816_);
lean_ctor_set(v___x_3813_, 0, v___x_3818_);
v___x_3820_ = v___x_3813_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_a_3816_);
v___x_3820_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
lean_ctor_set(v___x_3822_, 2, v___x_3821_);
lean_ctor_set(v___x_3822_, 3, v___x_3821_);
lean_ctor_set(v___x_3822_, 4, v___x_3821_);
lean_ctor_set(v___x_3822_, 5, v___x_3821_);
lean_inc(v_ref_3817_);
v___x_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_ref_3817_);
v___x_3824_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3825_ = 4;
v___x_3826_ = l_Lean_MessageData_nil;
v___x_3827_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3794_, v___x_3822_, v___x_3823_, v___x_3824_, v___x_3821_, v___x_3825_, v___x_3826_, v___y_3800_, v___y_3796_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; 
v_unused_3835_ = lean_ctor_get(v___x_3827_, 0);
lean_dec(v_unused_3835_);
v___x_3829_ = v___x_3827_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v___x_3827_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v_diag_3811_);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_diag_3811_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v_diag_3811_);
v_a_3836_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3827_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3827_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_del_object(v___x_3813_);
lean_dec_ref(v_diag_3811_);
lean_dec(v_tk_3794_);
v_a_3845_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3815_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3815_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v___y_3799_);
lean_dec(v_tk_3794_);
v_a_3854_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3808_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3808_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
v___jp_3862_:
{
if (lean_obj_tag(v___y_3869_) == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3876_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set_uint8(v___x_3876_, sizeof(void*)*1, v___x_3779_);
v___y_3796_ = v___y_3864_;
v___y_3797_ = v___y_3863_;
v___y_3798_ = v___y_3865_;
v___y_3799_ = v___y_3867_;
v___y_3800_ = v___y_3866_;
v___y_3801_ = v___y_3868_;
v___y_3802_ = v___y_3874_;
v___y_3803_ = v___y_3870_;
v___y_3804_ = v___y_3871_;
v___y_3805_ = v___y_3873_;
v___y_3806_ = v___y_3872_;
v___y_3807_ = v___x_3876_;
goto v___jp_3795_;
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3878_; 
v_val_3877_ = lean_ctor_get(v___y_3869_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v___y_3869_, 1);
v___x_3878_ = l_Lean_Elab_Tactic_expandLocation(v_val_3877_);
lean_dec(v_val_3877_);
v___y_3796_ = v___y_3864_;
v___y_3797_ = v___y_3863_;
v___y_3798_ = v___y_3865_;
v___y_3799_ = v___y_3867_;
v___y_3800_ = v___y_3866_;
v___y_3801_ = v___y_3868_;
v___y_3802_ = v___y_3874_;
v___y_3803_ = v___y_3870_;
v___y_3804_ = v___y_3871_;
v___y_3805_ = v___y_3873_;
v___y_3806_ = v___y_3872_;
v___y_3807_ = v___x_3878_;
goto v___jp_3795_;
}
}
v___jp_3879_:
{
uint8_t v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3891_ = 0;
v___x_3892_ = 2;
v___x_3893_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3894_ = lean_box(v___x_3891_);
v___x_3895_ = lean_box(v___x_3892_);
v___x_3896_ = lean_box(v___x_3891_);
lean_inc(v_stx_3882_);
v___x_3897_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3897_, 0, v_stx_3882_);
lean_closure_set(v___x_3897_, 1, v___x_3894_);
lean_closure_set(v___x_3897_, 2, v___x_3895_);
lean_closure_set(v___x_3897_, 3, v___x_3896_);
lean_closure_set(v___x_3897_, 4, v___x_3893_);
v___x_3898_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3897_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
if (lean_obj_tag(v___y_3881_) == 0)
{
lean_object* v_ctx_3900_; lean_object* v_simprocs_3901_; 
v_ctx_3900_ = lean_ctor_get(v_a_3899_, 0);
lean_inc_ref(v_ctx_3900_);
v_simprocs_3901_ = lean_ctor_get(v_a_3899_, 1);
lean_inc_ref(v_simprocs_3901_);
lean_dec(v_a_3899_);
v___y_3863_ = v___y_3884_;
v___y_3864_ = v___y_3890_;
v___y_3865_ = v___y_3885_;
v___y_3866_ = v___y_3889_;
v___y_3867_ = v_stx_3882_;
v___y_3868_ = v___y_3887_;
v___y_3869_ = v___y_3880_;
v___y_3870_ = v___y_3888_;
v___y_3871_ = v_simprocs_3901_;
v___y_3872_ = v___y_3883_;
v___y_3873_ = v___y_3886_;
v___y_3874_ = v_ctx_3900_;
goto v___jp_3862_;
}
else
{
lean_object* v_ctx_3902_; lean_object* v_simprocs_3903_; lean_object* v___x_3904_; 
lean_dec_ref_known(v___y_3881_, 1);
v_ctx_3902_ = lean_ctor_get(v_a_3899_, 0);
lean_inc_ref(v_ctx_3902_);
v_simprocs_3903_ = lean_ctor_get(v_a_3899_, 1);
lean_inc_ref(v_simprocs_3903_);
lean_dec(v_a_3899_);
v___x_3904_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3902_);
v___y_3863_ = v___y_3884_;
v___y_3864_ = v___y_3890_;
v___y_3865_ = v___y_3885_;
v___y_3866_ = v___y_3889_;
v___y_3867_ = v_stx_3882_;
v___y_3868_ = v___y_3887_;
v___y_3869_ = v___y_3880_;
v___y_3870_ = v___y_3888_;
v___y_3871_ = v_simprocs_3903_;
v___y_3872_ = v___y_3883_;
v___y_3873_ = v___y_3886_;
v___y_3874_ = v___x_3904_;
goto v___jp_3862_;
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_stx_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v_tk_3794_);
v_a_3905_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3898_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3898_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
v___jp_3913_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_inc_ref(v___y_3919_);
v___x_3934_ = l_Array_append___redArg(v___y_3919_, v___y_3933_);
lean_dec_ref(v___y_3933_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
v___x_3935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3935_, 0, v___y_3926_);
lean_ctor_set(v___x_3935_, 1, v___y_3927_);
lean_ctor_set(v___x_3935_, 2, v___x_3934_);
v___x_3936_ = l_Lean_Syntax_node6(v___y_3926_, v___y_3914_, v___y_3928_, v___y_3915_, v___y_3922_, v___y_3923_, v___y_3931_, v___x_3935_);
v___y_3880_ = v___y_3917_;
v___y_3881_ = v___y_3918_;
v_stx_3882_ = v___x_3936_;
v___y_3883_ = v___y_3916_;
v___y_3884_ = v___y_3925_;
v___y_3885_ = v___y_3929_;
v___y_3886_ = v___y_3932_;
v___y_3887_ = v___y_3921_;
v___y_3888_ = v___y_3924_;
v___y_3889_ = v___y_3930_;
v___y_3890_ = v___y_3920_;
goto v___jp_3879_;
}
v___jp_3937_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_inc_ref(v___y_3943_);
v___x_3957_ = l_Array_append___redArg(v___y_3943_, v___y_3956_);
lean_dec_ref(v___y_3956_);
lean_inc(v___y_3953_);
lean_inc(v___y_3952_);
v___x_3958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3958_, 0, v___y_3952_);
lean_ctor_set(v___x_3958_, 1, v___y_3953_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
if (lean_obj_tag(v___y_3941_) == 0)
{
lean_object* v___x_3959_; 
v___x_3959_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3914_ = v___y_3938_;
v___y_3915_ = v___y_3939_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3941_;
v___y_3918_ = v___y_3942_;
v___y_3919_ = v___y_3943_;
v___y_3920_ = v___y_3944_;
v___y_3921_ = v___y_3945_;
v___y_3922_ = v___y_3946_;
v___y_3923_ = v___y_3947_;
v___y_3924_ = v___y_3948_;
v___y_3925_ = v___y_3949_;
v___y_3926_ = v___y_3952_;
v___y_3927_ = v___y_3953_;
v___y_3928_ = v___y_3951_;
v___y_3929_ = v___y_3950_;
v___y_3930_ = v___y_3954_;
v___y_3931_ = v___x_3958_;
v___y_3932_ = v___y_3955_;
v___y_3933_ = v___x_3959_;
goto v___jp_3913_;
}
else
{
lean_object* v_val_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_val_3960_ = lean_ctor_get(v___y_3941_, 0);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_3960_);
v___x_3962_ = lean_array_push(v___x_3961_, v_val_3960_);
v___y_3914_ = v___y_3938_;
v___y_3915_ = v___y_3939_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3941_;
v___y_3918_ = v___y_3942_;
v___y_3919_ = v___y_3943_;
v___y_3920_ = v___y_3944_;
v___y_3921_ = v___y_3945_;
v___y_3922_ = v___y_3946_;
v___y_3923_ = v___y_3947_;
v___y_3924_ = v___y_3948_;
v___y_3925_ = v___y_3949_;
v___y_3926_ = v___y_3952_;
v___y_3927_ = v___y_3953_;
v___y_3928_ = v___y_3951_;
v___y_3929_ = v___y_3950_;
v___y_3930_ = v___y_3954_;
v___y_3931_ = v___x_3958_;
v___y_3932_ = v___y_3955_;
v___y_3933_ = v___x_3962_;
goto v___jp_3913_;
}
}
v___jp_3963_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_inc_ref(v___y_3969_);
v___x_3983_ = l_Array_append___redArg(v___y_3969_, v___y_3982_);
lean_dec_ref(v___y_3982_);
lean_inc(v___y_3979_);
lean_inc(v___y_3978_);
v___x_3984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3984_, 0, v___y_3978_);
lean_ctor_set(v___x_3984_, 1, v___y_3979_);
lean_ctor_set(v___x_3984_, 2, v___x_3983_);
if (lean_obj_tag(v___y_3973_) == 1)
{
lean_object* v_val_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_val_3985_ = lean_ctor_get(v___y_3973_, 0);
lean_inc(v_val_3985_);
lean_dec_ref_known(v___y_3973_, 1);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_3978_, 3);
v___x_3987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___y_3978_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
lean_inc_ref(v___y_3969_);
v___x_3988_ = l_Array_append___redArg(v___y_3969_, v_val_3985_);
lean_dec(v_val_3985_);
lean_inc(v___y_3979_);
v___x_3989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3989_, 0, v___y_3978_);
lean_ctor_set(v___x_3989_, 1, v___y_3979_);
lean_ctor_set(v___x_3989_, 2, v___x_3988_);
v___x_3990_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___y_3978_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = l_Array_mkArray3___redArg(v___x_3987_, v___x_3989_, v___x_3991_);
v___y_3938_ = v___y_3964_;
v___y_3939_ = v___y_3965_;
v___y_3940_ = v___y_3966_;
v___y_3941_ = v___y_3967_;
v___y_3942_ = v___y_3968_;
v___y_3943_ = v___y_3969_;
v___y_3944_ = v___y_3970_;
v___y_3945_ = v___y_3971_;
v___y_3946_ = v___y_3972_;
v___y_3947_ = v___x_3984_;
v___y_3948_ = v___y_3974_;
v___y_3949_ = v___y_3975_;
v___y_3950_ = v___y_3977_;
v___y_3951_ = v___y_3976_;
v___y_3952_ = v___y_3978_;
v___y_3953_ = v___y_3979_;
v___y_3954_ = v___y_3980_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___x_3992_;
goto v___jp_3937_;
}
else
{
lean_object* v___x_3993_; 
lean_dec(v___y_3973_);
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3938_ = v___y_3964_;
v___y_3939_ = v___y_3965_;
v___y_3940_ = v___y_3966_;
v___y_3941_ = v___y_3967_;
v___y_3942_ = v___y_3968_;
v___y_3943_ = v___y_3969_;
v___y_3944_ = v___y_3970_;
v___y_3945_ = v___y_3971_;
v___y_3946_ = v___y_3972_;
v___y_3947_ = v___x_3984_;
v___y_3948_ = v___y_3974_;
v___y_3949_ = v___y_3975_;
v___y_3950_ = v___y_3977_;
v___y_3951_ = v___y_3976_;
v___y_3952_ = v___y_3978_;
v___y_3953_ = v___y_3979_;
v___y_3954_ = v___y_3980_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___x_3993_;
goto v___jp_3937_;
}
}
v___jp_3994_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_inc_ref(v___y_4001_);
v___x_4015_ = l_Array_append___redArg(v___y_4001_, v___y_4014_);
lean_dec_ref(v___y_4014_);
lean_inc(v___y_3997_);
lean_inc(v___y_4007_);
v___x_4016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4016_, 0, v___y_4007_);
lean_ctor_set(v___x_4016_, 1, v___y_3997_);
lean_ctor_set(v___x_4016_, 2, v___x_4015_);
v___x_4017_ = l_Lean_Syntax_node6(v___y_4007_, v___y_4008_, v___y_4005_, v___y_3995_, v___y_4012_, v___y_4002_, v___y_3998_, v___x_4016_);
v___y_3880_ = v___y_3999_;
v___y_3881_ = v___y_4000_;
v_stx_3882_ = v___x_4017_;
v___y_3883_ = v___y_3996_;
v___y_3884_ = v___y_4009_;
v___y_3885_ = v___y_4010_;
v___y_3886_ = v___y_4013_;
v___y_3887_ = v___y_4004_;
v___y_3888_ = v___y_4006_;
v___y_3889_ = v___y_4011_;
v___y_3890_ = v___y_4003_;
goto v___jp_3879_;
}
v___jp_4018_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_inc_ref(v___y_4024_);
v___x_4038_ = l_Array_append___redArg(v___y_4024_, v___y_4037_);
lean_dec_ref(v___y_4037_);
lean_inc(v___y_4021_);
lean_inc(v___y_4031_);
v___x_4039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4039_, 0, v___y_4031_);
lean_ctor_set(v___x_4039_, 1, v___y_4021_);
lean_ctor_set(v___x_4039_, 2, v___x_4038_);
if (lean_obj_tag(v___y_4022_) == 0)
{
lean_object* v___x_4040_; 
v___x_4040_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3995_ = v___y_4019_;
v___y_3996_ = v___y_4020_;
v___y_3997_ = v___y_4021_;
v___y_3998_ = v___x_4039_;
v___y_3999_ = v___y_4022_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___y_4024_;
v___y_4002_ = v___y_4025_;
v___y_4003_ = v___y_4026_;
v___y_4004_ = v___y_4027_;
v___y_4005_ = v___y_4028_;
v___y_4006_ = v___y_4029_;
v___y_4007_ = v___y_4031_;
v___y_4008_ = v___y_4030_;
v___y_4009_ = v___y_4032_;
v___y_4010_ = v___y_4033_;
v___y_4011_ = v___y_4035_;
v___y_4012_ = v___y_4034_;
v___y_4013_ = v___y_4036_;
v___y_4014_ = v___x_4040_;
goto v___jp_3994_;
}
else
{
lean_object* v_val_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_val_4041_ = lean_ctor_get(v___y_4022_, 0);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4041_);
v___x_4043_ = lean_array_push(v___x_4042_, v_val_4041_);
v___y_3995_ = v___y_4019_;
v___y_3996_ = v___y_4020_;
v___y_3997_ = v___y_4021_;
v___y_3998_ = v___x_4039_;
v___y_3999_ = v___y_4022_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___y_4024_;
v___y_4002_ = v___y_4025_;
v___y_4003_ = v___y_4026_;
v___y_4004_ = v___y_4027_;
v___y_4005_ = v___y_4028_;
v___y_4006_ = v___y_4029_;
v___y_4007_ = v___y_4031_;
v___y_4008_ = v___y_4030_;
v___y_4009_ = v___y_4032_;
v___y_4010_ = v___y_4033_;
v___y_4011_ = v___y_4035_;
v___y_4012_ = v___y_4034_;
v___y_4013_ = v___y_4036_;
v___y_4014_ = v___x_4043_;
goto v___jp_3994_;
}
}
v___jp_4044_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_inc_ref(v___y_4050_);
v___x_4064_ = l_Array_append___redArg(v___y_4050_, v___y_4063_);
lean_dec_ref(v___y_4063_);
lean_inc(v___y_4047_);
lean_inc(v___y_4056_);
v___x_4065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___y_4056_);
lean_ctor_set(v___x_4065_, 1, v___y_4047_);
lean_ctor_set(v___x_4065_, 2, v___x_4064_);
if (lean_obj_tag(v___y_4054_) == 1)
{
lean_object* v_val_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_val_4066_ = lean_ctor_get(v___y_4054_, 0);
lean_inc(v_val_4066_);
lean_dec_ref_known(v___y_4054_, 1);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4056_, 3);
v___x_4068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___y_4056_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
lean_inc_ref(v___y_4050_);
v___x_4069_ = l_Array_append___redArg(v___y_4050_, v_val_4066_);
lean_dec(v_val_4066_);
lean_inc(v___y_4047_);
v___x_4070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4070_, 0, v___y_4056_);
lean_ctor_set(v___x_4070_, 1, v___y_4047_);
lean_ctor_set(v___x_4070_, 2, v___x_4069_);
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___y_4056_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Array_mkArray3___redArg(v___x_4068_, v___x_4070_, v___x_4072_);
v___y_4019_ = v___y_4045_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___y_4047_;
v___y_4022_ = v___y_4048_;
v___y_4023_ = v___y_4049_;
v___y_4024_ = v___y_4050_;
v___y_4025_ = v___x_4065_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4058_;
v___y_4033_ = v___y_4059_;
v___y_4034_ = v___y_4061_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4062_;
v___y_4037_ = v___x_4073_;
goto v___jp_4018_;
}
else
{
lean_object* v___x_4074_; 
lean_dec(v___y_4054_);
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4019_ = v___y_4045_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___y_4047_;
v___y_4022_ = v___y_4048_;
v___y_4023_ = v___y_4049_;
v___y_4024_ = v___y_4050_;
v___y_4025_ = v___x_4065_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4058_;
v___y_4033_ = v___y_4059_;
v___y_4034_ = v___y_4061_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4062_;
v___y_4037_ = v___x_4074_;
goto v___jp_4018_;
}
}
v___jp_4075_:
{
if (lean_obj_tag(v___y_4078_) == 0)
{
lean_object* v_ref_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_ref_4089_ = lean_ctor_get(v___y_4086_, 2);
v___x_4090_ = 0;
v___x_4091_ = l_Lean_SourceInfo_fromRef(v_ref_4089_, v___x_4090_);
v___x_4092_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4093_ = l_Lean_Name_mkStr4(v___x_3780_, v___x_3781_, v___x_3782_, v___x_4092_);
v___x_4094_ = l_Lean_SourceInfo_fromRef(v_tk_3794_, v___x_3779_);
v___x_4095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___x_4092_);
v___x_4096_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4097_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4091_);
v___x_4098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4091_);
lean_ctor_set(v___x_4098_, 1, v___x_4096_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
if (lean_obj_tag(v___y_4079_) == 1)
{
lean_object* v_val_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v_val_4099_ = lean_ctor_get(v___y_4079_, 0);
lean_inc(v_val_4099_);
lean_dec_ref_known(v___y_4079_, 1);
v___x_4100_ = l_Lean_SourceInfo_fromRef(v_val_4099_, v___x_3779_);
lean_dec(v_val_4099_);
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = l_Array_mkArray1___redArg(v___x_4102_);
v___y_3964_ = v___x_4093_;
v___y_3965_ = v___y_4076_;
v___y_3966_ = v___y_4077_;
v___y_3967_ = v___y_4088_;
v___y_3968_ = v___y_4078_;
v___y_3969_ = v___x_4097_;
v___y_3970_ = v___y_4080_;
v___y_3971_ = v___y_4081_;
v___y_3972_ = v___x_4098_;
v___y_3973_ = v___y_4082_;
v___y_3974_ = v___y_4083_;
v___y_3975_ = v___y_4084_;
v___y_3976_ = v___x_4095_;
v___y_3977_ = v___y_4085_;
v___y_3978_ = v___x_4091_;
v___y_3979_ = v___x_4096_;
v___y_3980_ = v___y_4086_;
v___y_3981_ = v___y_4087_;
v___y_3982_ = v___x_4103_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_4104_; 
lean_dec(v___y_4079_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3964_ = v___x_4093_;
v___y_3965_ = v___y_4076_;
v___y_3966_ = v___y_4077_;
v___y_3967_ = v___y_4088_;
v___y_3968_ = v___y_4078_;
v___y_3969_ = v___x_4097_;
v___y_3970_ = v___y_4080_;
v___y_3971_ = v___y_4081_;
v___y_3972_ = v___x_4098_;
v___y_3973_ = v___y_4082_;
v___y_3974_ = v___y_4083_;
v___y_3975_ = v___y_4084_;
v___y_3976_ = v___x_4095_;
v___y_3977_ = v___y_4085_;
v___y_3978_ = v___x_4091_;
v___y_3979_ = v___x_4096_;
v___y_3980_ = v___y_4086_;
v___y_3981_ = v___y_4087_;
v___y_3982_ = v___x_4104_;
goto v___jp_3963_;
}
}
else
{
lean_object* v_ref_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v_ref_4105_ = lean_ctor_get(v___y_4086_, 2);
v___x_4106_ = 0;
v___x_4107_ = l_Lean_SourceInfo_fromRef(v_ref_4105_, v___x_4106_);
v___x_4108_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4109_ = l_Lean_Name_mkStr4(v___x_3780_, v___x_3781_, v___x_3782_, v___x_4108_);
v___x_4110_ = l_Lean_SourceInfo_fromRef(v_tk_3794_, v___x_3779_);
v___x_4111_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4114_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4107_);
v___x_4115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4107_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
lean_ctor_set(v___x_4115_, 2, v___x_4114_);
if (lean_obj_tag(v___y_4079_) == 1)
{
lean_object* v_val_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_val_4116_ = lean_ctor_get(v___y_4079_, 0);
lean_inc(v_val_4116_);
lean_dec_ref_known(v___y_4079_, 1);
v___x_4117_ = l_Lean_SourceInfo_fromRef(v_val_4116_, v___x_3779_);
lean_dec(v_val_4116_);
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4117_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = l_Array_mkArray1___redArg(v___x_4119_);
v___y_4045_ = v___y_4076_;
v___y_4046_ = v___y_4077_;
v___y_4047_ = v___x_4113_;
v___y_4048_ = v___y_4088_;
v___y_4049_ = v___y_4078_;
v___y_4050_ = v___x_4114_;
v___y_4051_ = v___y_4080_;
v___y_4052_ = v___y_4081_;
v___y_4053_ = v___x_4112_;
v___y_4054_ = v___y_4082_;
v___y_4055_ = v___y_4083_;
v___y_4056_ = v___x_4107_;
v___y_4057_ = v___x_4109_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___x_4115_;
v___y_4062_ = v___y_4087_;
v___y_4063_ = v___x_4120_;
goto v___jp_4044_;
}
else
{
lean_object* v___x_4121_; 
lean_dec(v___y_4079_);
v___x_4121_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4045_ = v___y_4076_;
v___y_4046_ = v___y_4077_;
v___y_4047_ = v___x_4113_;
v___y_4048_ = v___y_4088_;
v___y_4049_ = v___y_4078_;
v___y_4050_ = v___x_4114_;
v___y_4051_ = v___y_4080_;
v___y_4052_ = v___y_4081_;
v___y_4053_ = v___x_4112_;
v___y_4054_ = v___y_4082_;
v___y_4055_ = v___y_4083_;
v___y_4056_ = v___x_4107_;
v___y_4057_ = v___x_4109_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___x_4115_;
v___y_4062_ = v___y_4087_;
v___y_4063_ = v___x_4121_;
goto v___jp_4044_;
}
}
}
v___jp_4122_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = lean_unsigned_to_nat(3u);
v___x_4137_ = l_Lean_Syntax_getArg(v___y_4126_, v___x_4136_);
lean_dec(v___y_4126_);
v___x_4138_ = l_Lean_Syntax_getOptional_x3f(v___x_4137_);
lean_dec(v___x_4137_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_box(0);
v___y_4076_ = v___y_4123_;
v___y_4077_ = v___y_4128_;
v___y_4078_ = v___y_4124_;
v___y_4079_ = v___y_4125_;
v___y_4080_ = v___y_4135_;
v___y_4081_ = v___y_4132_;
v___y_4082_ = v_args_4127_;
v___y_4083_ = v___y_4133_;
v___y_4084_ = v___y_4129_;
v___y_4085_ = v___y_4130_;
v___y_4086_ = v___y_4134_;
v___y_4087_ = v___y_4131_;
v___y_4088_ = v___x_4139_;
goto v___jp_4075_;
}
else
{
lean_object* v_val_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_val_4140_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4138_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_val_4140_);
lean_dec(v___x_4138_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_val_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
v___y_4076_ = v___y_4123_;
v___y_4077_ = v___y_4128_;
v___y_4078_ = v___y_4124_;
v___y_4079_ = v___y_4125_;
v___y_4080_ = v___y_4135_;
v___y_4081_ = v___y_4132_;
v___y_4082_ = v_args_4127_;
v___y_4083_ = v___y_4133_;
v___y_4084_ = v___y_4129_;
v___y_4085_ = v___y_4130_;
v___y_4086_ = v___y_4134_;
v___y_4087_ = v___y_4131_;
v___y_4088_ = v___x_4145_;
goto v___jp_4075_;
}
}
}
}
v___jp_4149_:
{
lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4163_ = l_Lean_Syntax_getArg(v___y_4153_, v___y_4151_);
v___x_4164_ = l_Lean_Syntax_isNone(v___x_4163_);
if (v___x_4164_ == 0)
{
uint8_t v___x_4165_; 
lean_inc(v___x_4163_);
v___x_4165_ = l_Lean_Syntax_matchesNull(v___x_4163_, v___x_4148_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v___x_4163_);
lean_dec(v_o_4154_);
lean_dec(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4150_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4166_;
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = l_Lean_Syntax_getArg(v___x_4163_, v___x_3793_);
lean_dec(v___x_4163_);
v___x_4168_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3782_);
lean_inc_ref(v___x_3781_);
lean_inc_ref(v___x_3780_);
v___x_4169_ = l_Lean_Name_mkStr4(v___x_3780_, v___x_3781_, v___x_3782_, v___x_4168_);
lean_inc(v___x_4167_);
v___x_4170_ = l_Lean_Syntax_isOfKind(v___x_4167_, v___x_4169_);
lean_dec(v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; 
lean_dec(v___x_4167_);
lean_dec(v_o_4154_);
lean_dec(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4150_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4171_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4171_;
}
else
{
lean_object* v___x_4172_; lean_object* v_args_4173_; lean_object* v___x_4174_; 
v___x_4172_ = l_Lean_Syntax_getArg(v___x_4167_, v___x_4148_);
lean_dec(v___x_4167_);
v_args_4173_ = l_Lean_Syntax_getArgs(v___x_4172_);
lean_dec(v___x_4172_);
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_args_4173_);
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v_o_4154_;
v___y_4126_ = v___y_4153_;
v_args_4127_ = v___x_4174_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
goto v___jp_4122_;
}
}
}
else
{
lean_object* v___x_4175_; 
lean_dec(v___x_4163_);
v___x_4175_ = lean_box(0);
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v_o_4154_;
v___y_4126_ = v___y_4153_;
v_args_4127_ = v___x_4175_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___y_4156_;
v___y_4130_ = v___y_4157_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
goto v___jp_4122_;
}
}
v___jp_4176_:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4186_ = lean_unsigned_to_nat(2u);
v___x_4187_ = l_Lean_Syntax_getArg(v_stx_3778_, v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3782_);
lean_inc_ref(v___x_3781_);
lean_inc_ref(v___x_3780_);
v___x_4189_ = l_Lean_Name_mkStr4(v___x_3780_, v___x_3781_, v___x_3782_, v___x_4188_);
lean_inc(v___x_4187_);
v___x_4190_ = l_Lean_Syntax_isOfKind(v___x_4187_, v___x_4189_);
lean_dec(v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; 
lean_dec(v___x_4187_);
lean_dec(v_bang_4177_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4191_;
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4192_ = l_Lean_Syntax_getArg(v___x_4187_, v___x_3793_);
v___x_4193_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3782_);
lean_inc_ref(v___x_3781_);
lean_inc_ref(v___x_3780_);
v___x_4194_ = l_Lean_Name_mkStr4(v___x_3780_, v___x_3781_, v___x_3782_, v___x_4193_);
lean_inc(v___x_4192_);
v___x_4195_ = l_Lean_Syntax_isOfKind(v___x_4192_, v___x_4194_);
lean_dec(v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
lean_dec(v___x_4192_);
lean_dec(v___x_4187_);
lean_dec(v_bang_4177_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4196_;
}
else
{
lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = l_Lean_Syntax_getArg(v___x_4187_, v___x_4148_);
v___x_4198_ = l_Lean_Syntax_isNone(v___x_4197_);
if (v___x_4198_ == 0)
{
uint8_t v___x_4199_; 
lean_inc(v___x_4197_);
v___x_4199_ = l_Lean_Syntax_matchesNull(v___x_4197_, v___x_4148_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; 
lean_dec(v___x_4197_);
lean_dec(v___x_4192_);
lean_dec(v___x_4187_);
lean_dec(v_bang_4177_);
lean_dec(v_tk_3794_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
lean_dec_ref(v___x_3780_);
v___x_4200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4200_;
}
else
{
lean_object* v_o_4201_; lean_object* v___x_4202_; 
v_o_4201_ = l_Lean_Syntax_getArg(v___x_4197_, v___x_3793_);
lean_dec(v___x_4197_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v_o_4201_);
v___y_4150_ = v___x_4192_;
v___y_4151_ = v___x_4186_;
v___y_4152_ = v_bang_4177_;
v___y_4153_ = v___x_4187_;
v_o_4154_ = v___x_4202_;
v___y_4155_ = v___y_4178_;
v___y_4156_ = v___y_4179_;
v___y_4157_ = v___y_4180_;
v___y_4158_ = v___y_4181_;
v___y_4159_ = v___y_4182_;
v___y_4160_ = v___y_4183_;
v___y_4161_ = v___y_4184_;
v___y_4162_ = v___y_4185_;
goto v___jp_4149_;
}
}
else
{
lean_object* v___x_4203_; 
lean_dec(v___x_4197_);
v___x_4203_ = lean_box(0);
v___y_4150_ = v___x_4192_;
v___y_4151_ = v___x_4186_;
v___y_4152_ = v_bang_4177_;
v___y_4153_ = v___x_4187_;
v_o_4154_ = v___x_4203_;
v___y_4155_ = v___y_4178_;
v___y_4156_ = v___y_4179_;
v___y_4157_ = v___y_4180_;
v___y_4158_ = v___y_4181_;
v___y_4159_ = v___y_4182_;
v___y_4160_ = v___y_4183_;
v___y_4161_ = v___y_4184_;
v___y_4162_ = v___y_4185_;
goto v___jp_4149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4211_, lean_object* v_stx_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___x_8015__boxed_4226_; uint8_t v___x_8016__boxed_4227_; lean_object* v_res_4228_; 
v___x_8015__boxed_4226_ = lean_unbox(v___x_4211_);
v___x_8016__boxed_4227_ = lean_unbox(v___x_4213_);
v_res_4228_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8015__boxed_4226_, v_stx_4212_, v___x_8016__boxed_4227_, v___x_4214_, v___x_4215_, v___x_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v_stx_4212_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; uint8_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___y_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4235_);
v___x_4249_ = l_Lean_Syntax_isOfKind(v_stx_4235_, v___x_4248_);
v___x_4250_ = 1;
v___x_4251_ = lean_box(v___x_4249_);
v___x_4252_ = lean_box(v___x_4250_);
v___y_4253_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4253_, 0, v___x_4251_);
lean_closure_set(v___y_4253_, 1, v_stx_4235_);
lean_closure_set(v___y_4253_, 2, v___x_4252_);
lean_closure_set(v___y_4253_, 3, v___x_4245_);
lean_closure_set(v___y_4253_, 4, v___x_4246_);
lean_closure_set(v___y_4253_, 5, v___x_4247_);
v___x_4254_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4254_, 0, v___y_4253_);
v___x_4255_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4254_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4274_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4277_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4274_, v___x_4275_, v___x_4276_, v___x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4309_ = l_Lean_addBuiltinDeclarationRanges(v___x_4307_, v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4311_;
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
