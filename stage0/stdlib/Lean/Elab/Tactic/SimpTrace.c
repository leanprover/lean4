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
lean_object* l_Array_mkArray0(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp_all!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpAllTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value;
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
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___y_25_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_uget_borrowed(v_as_12_, v_i_13_);
v___x_27_ = l_Lean_Syntax_getArg(v___x_23_, v___x_22_);
lean_inc(v___x_23_);
v___x_28_ = l_Lean_Syntax_getKind(v___x_23_);
if (lean_obj_tag(v___x_28_) == 1)
{
lean_object* v_pre_29_; 
v_pre_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_pre_29_);
if (lean_obj_tag(v_pre_29_) == 1)
{
lean_object* v_pre_30_; 
v_pre_30_ = lean_ctor_get(v_pre_29_, 0);
lean_inc(v_pre_30_);
if (lean_obj_tag(v_pre_30_) == 1)
{
lean_object* v_pre_31_; 
v_pre_31_ = lean_ctor_get(v_pre_30_, 0);
lean_inc(v_pre_31_);
if (lean_obj_tag(v_pre_31_) == 1)
{
lean_object* v_pre_32_; 
v_pre_32_ = lean_ctor_get(v_pre_31_, 0);
if (lean_obj_tag(v_pre_32_) == 0)
{
lean_object* v_str_33_; lean_object* v_str_34_; lean_object* v_str_35_; lean_object* v_str_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_str_33_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_str_33_);
lean_dec_ref_known(v___x_28_, 2);
v_str_34_ = lean_ctor_get(v_pre_29_, 1);
lean_inc_ref(v_str_34_);
lean_dec_ref_known(v_pre_29_, 2);
v_str_35_ = lean_ctor_get(v_pre_30_, 1);
lean_inc_ref(v_str_35_);
lean_dec_ref_known(v_pre_30_, 2);
v_str_36_ = lean_ctor_get(v_pre_31_, 1);
lean_inc_ref(v_str_36_);
lean_dec_ref_known(v_pre_31_, 2);
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_38_ = lean_string_dec_eq(v_str_36_, v___x_37_);
lean_dec_ref(v_str_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_str_35_);
lean_dec_ref(v_str_34_);
lean_dec_ref(v_str_33_);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_39_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_39_;
goto v___jp_16_;
}
else
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_41_ = lean_string_dec_eq(v_str_35_, v___x_40_);
lean_dec_ref(v_str_35_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v_str_34_);
lean_dec_ref(v_str_33_);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_42_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_42_;
goto v___jp_16_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_44_ = lean_string_dec_eq(v_str_34_, v___x_43_);
lean_dec_ref(v_str_34_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec_ref(v_str_33_);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_45_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_45_;
goto v___jp_16_;
}
else
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3));
v___x_47_ = lean_string_dec_eq(v_str_33_, v___x_46_);
lean_dec_ref(v_str_33_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_48_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_48_;
goto v___jp_16_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = l_Lean_Syntax_getArg(v___x_27_, v___x_49_);
v___x_51_ = l_Lean_Syntax_getKind(v___x_27_);
if (lean_obj_tag(v___x_51_) == 1)
{
lean_object* v_pre_52_; 
v_pre_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_pre_52_);
if (lean_obj_tag(v_pre_52_) == 1)
{
lean_object* v_pre_53_; 
v_pre_53_ = lean_ctor_get(v_pre_52_, 0);
lean_inc(v_pre_53_);
if (lean_obj_tag(v_pre_53_) == 1)
{
lean_object* v_pre_54_; 
v_pre_54_ = lean_ctor_get(v_pre_53_, 0);
lean_inc(v_pre_54_);
if (lean_obj_tag(v_pre_54_) == 1)
{
lean_object* v_pre_55_; 
v_pre_55_ = lean_ctor_get(v_pre_54_, 0);
if (lean_obj_tag(v_pre_55_) == 0)
{
lean_object* v_str_56_; lean_object* v_str_57_; lean_object* v_str_58_; lean_object* v_str_59_; uint8_t v___x_60_; 
v_str_56_ = lean_ctor_get(v___x_51_, 1);
lean_inc_ref(v_str_56_);
lean_dec_ref_known(v___x_51_, 2);
v_str_57_ = lean_ctor_get(v_pre_52_, 1);
lean_inc_ref(v_str_57_);
lean_dec_ref_known(v_pre_52_, 2);
v_str_58_ = lean_ctor_get(v_pre_53_, 1);
lean_inc_ref(v_str_58_);
lean_dec_ref_known(v_pre_53_, 2);
v_str_59_ = lean_ctor_get(v_pre_54_, 1);
lean_inc_ref(v_str_59_);
lean_dec_ref_known(v_pre_54_, 2);
v___x_60_ = lean_string_dec_eq(v_str_59_, v___x_37_);
lean_dec_ref(v_str_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref(v_str_58_);
lean_dec_ref(v_str_57_);
lean_dec_ref(v_str_56_);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_61_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_61_;
goto v___jp_16_;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = lean_string_dec_eq(v_str_58_, v___x_40_);
lean_dec_ref(v_str_58_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_str_57_);
lean_dec_ref(v_str_56_);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_63_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_63_;
goto v___jp_16_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = lean_string_dec_eq(v_str_57_, v___x_43_);
lean_dec_ref(v_str_57_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v_str_56_);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_65_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_65_;
goto v___jp_16_;
}
else
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4));
v___x_67_ = lean_string_dec_eq(v_str_56_, v___x_66_);
lean_dec_ref(v_str_56_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_68_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_68_;
goto v___jp_16_;
}
else
{
lean_object* v___x_69_; lean_object* v_id_70_; lean_object* v___x_71_; uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_69_ = l_Lean_Syntax_getId(v___x_50_);
lean_dec(v___x_50_);
v_id_70_ = l_Lean_Name_eraseMacroScopes(v___x_69_);
lean_dec(v___x_69_);
v___x_71_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6));
v___x_72_ = lean_name_eq(v_id_70_, v___x_71_);
v___x_73_ = lean_bool_not(v___x_72_);
if (v___x_73_ == 0)
{
lean_dec(v_id_70_);
v___y_25_ = v___x_73_;
goto v___jp_24_;
}
else
{
lean_object* v___x_74_; uint8_t v___x_75_; uint8_t v___x_76_; 
v___x_74_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8));
v___x_75_ = lean_name_eq(v_id_70_, v___x_74_);
lean_dec(v_id_70_);
v___x_76_ = lean_bool_not(v___x_75_);
v___y_25_ = v___x_76_;
goto v___jp_24_;
}
}
}
}
}
}
else
{
lean_object* v___x_77_; 
lean_dec_ref_known(v_pre_54_, 2);
lean_dec_ref_known(v_pre_53_, 2);
lean_dec_ref_known(v_pre_52_, 2);
lean_dec_ref_known(v___x_51_, 2);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_77_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_77_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec_ref_known(v_pre_53_, 2);
lean_dec(v_pre_54_);
lean_dec_ref_known(v_pre_52_, 2);
lean_dec_ref_known(v___x_51_, 2);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_78_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_78_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec_ref_known(v_pre_52_, 2);
lean_dec(v_pre_53_);
lean_dec_ref_known(v___x_51_, 2);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_79_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_79_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_pre_52_);
lean_dec_ref_known(v___x_51_, 2);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_80_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_80_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v___x_51_);
lean_dec(v___x_50_);
lean_inc(v___x_23_);
v___x_81_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_81_;
goto v___jp_16_;
}
}
}
}
}
}
else
{
lean_object* v___x_82_; 
lean_dec_ref_known(v_pre_31_, 2);
lean_dec_ref_known(v_pre_30_, 2);
lean_dec_ref_known(v_pre_29_, 2);
lean_dec_ref_known(v___x_28_, 2);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_82_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_82_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_83_; 
lean_dec_ref_known(v_pre_30_, 2);
lean_dec(v_pre_31_);
lean_dec_ref_known(v_pre_29_, 2);
lean_dec_ref_known(v___x_28_, 2);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_83_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_83_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_84_; 
lean_dec_ref_known(v_pre_29_, 2);
lean_dec(v_pre_30_);
lean_dec_ref_known(v___x_28_, 2);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_84_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_84_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_85_; 
lean_dec_ref_known(v___x_28_, 2);
lean_dec(v_pre_29_);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_85_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_85_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v___x_28_);
lean_dec(v___x_27_);
lean_inc(v___x_23_);
v___x_86_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_86_;
goto v___jp_16_;
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
else
{
lean_object* v___x_26_; 
lean_inc(v___x_23_);
v___x_26_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_26_;
goto v___jp_16_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object* v_as_87_, lean_object* v_i_88_, lean_object* v_stop_89_, lean_object* v_b_90_){
_start:
{
size_t v_i_boxed_91_; size_t v_stop_boxed_92_; lean_object* v_res_93_; 
v_i_boxed_91_ = lean_unbox_usize(v_i_88_);
lean_dec(v_i_88_);
v_stop_boxed_92_ = lean_unbox_usize(v_stop_89_);
lean_dec(v_stop_89_);
v_res_93_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_87_, v_i_boxed_91_, v_stop_boxed_92_, v_b_90_);
lean_dec_ref(v_as_87_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object* v_cfg_96_){
_start:
{
lean_object* v___x_98_; lean_object* v_nullNode_99_; lean_object* v___y_101_; lean_object* v_configItems_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v_nullNode_99_ = l_Lean_Syntax_getArg(v_cfg_96_, v___x_98_);
v_configItems_105_ = l_Lean_Syntax_getArgs(v_nullNode_99_);
v___x_106_ = lean_array_get_size(v_configItems_105_);
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_108_ = lean_nat_dec_lt(v___x_98_, v___x_106_);
if (v___x_108_ == 0)
{
lean_dec_ref(v_configItems_105_);
v___y_101_ = v___x_107_;
goto v___jp_100_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = lean_nat_dec_le(v___x_106_, v___x_106_);
if (v___x_109_ == 0)
{
if (v___x_108_ == 0)
{
lean_dec_ref(v_configItems_105_);
v___y_101_ = v___x_107_;
goto v___jp_100_;
}
else
{
size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((size_t)0ULL);
v___x_111_ = lean_usize_of_nat(v___x_106_);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_105_, v___x_110_, v___x_111_, v___x_107_);
lean_dec_ref(v_configItems_105_);
v___y_101_ = v___x_112_;
goto v___jp_100_;
}
}
else
{
size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v___x_113_ = ((size_t)0ULL);
v___x_114_ = lean_usize_of_nat(v___x_106_);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_105_, v___x_113_, v___x_114_, v___x_107_);
lean_dec_ref(v_configItems_105_);
v___y_101_ = v___x_115_;
goto v___jp_100_;
}
}
v___jp_100_:
{
lean_object* v_newNullNode_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_newNullNode_102_ = l_Lean_Syntax_setArgs(v_nullNode_99_, v___y_101_);
v___x_103_ = l_Lean_Syntax_setArg(v_cfg_96_, v___x_98_, v_newNullNode_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_119_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_133_, lean_object* v_usedSimps_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_stx_140_; lean_object* v___x_141_; 
v_stx_140_ = l_Lean_Syntax_unsetTrailing(v_stx_133_);
v___x_141_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_140_, v_usedSimps_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
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
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_141_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_158_, lean_object* v_usedSimps_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_158_, v_usedSimps_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec_ref(v_usedSimps_159_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(v___x_196_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_205_, lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v___x_38791__boxed_212_; lean_object* v_res_213_; 
v___x_38791__boxed_212_ = lean_unbox(v___x_205_);
v_res_213_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38791__boxed_212_, v_x_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v_x_206_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_214_, lean_object* v___x_215_, uint8_t v___x_216_, lean_object* v___y_217_, lean_object* v_simprocs_218_, lean_object* v_discharge_x3f_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
if (lean_obj_tag(v___y_214_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_mk_empty_array_with_capacity(v___x_215_);
v___x_230_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_216_);
v___x_231_ = l_Lean_Elab_Tactic_simpLocation(v___y_217_, v_simprocs_218_, v_discharge_x3f_219_, v___x_230_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_val_232_ = lean_ctor_get(v___y_214_, 0);
v___x_233_ = l_Lean_Elab_Tactic_expandLocation(v_val_232_);
v___x_234_ = l_Lean_Elab_Tactic_simpLocation(v___y_217_, v_simprocs_218_, v_discharge_x3f_219_, v___x_233_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_235_, lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v___y_238_, lean_object* v_simprocs_239_, lean_object* v_discharge_x3f_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v___x_38818__boxed_250_; lean_object* v_res_251_; 
v___x_38818__boxed_250_ = lean_unbox(v___x_237_);
v_res_251_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_235_, v___x_236_, v___x_38818__boxed_250_, v___y_238_, v_simprocs_239_, v_discharge_x3f_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___x_236_);
lean_dec(v___y_235_);
return v_res_251_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Array_mkArray0(lean_box(0));
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_262_, lean_object* v_as_x27_263_, lean_object* v_b_264_, lean_object* v___y_265_){
_start:
{
if (lean_obj_tag(v_as_x27_263_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_264_);
return v___x_267_;
}
else
{
lean_object* v_head_268_; lean_object* v_tail_269_; lean_object* v_ref_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_head_268_ = lean_ctor_get(v_as_x27_263_, 0);
v_tail_269_ = lean_ctor_get(v_as_x27_263_, 1);
v_ref_270_ = lean_ctor_get(v___y_265_, 5);
v___x_271_ = 1;
v___x_272_ = 0;
v___x_273_ = l_Lean_SourceInfo_fromRef(v_ref_270_, v___x_272_);
v___x_274_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_275_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_276_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_273_);
v___x_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_277_, 0, v___x_273_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_inc(v_head_268_);
v___x_278_ = l_Lean_mkCIdentFrom(v___x_262_, v_head_268_, v___x_271_);
lean_inc_ref(v___x_277_);
v___x_279_ = l_Lean_Syntax_node3(v___x_273_, v___x_274_, v___x_277_, v___x_277_, v___x_278_);
v___x_280_ = lean_array_push(v_b_264_, v___x_279_);
v_as_x27_263_ = v_tail_269_;
v_b_264_ = v___x_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_282_, lean_object* v_as_x27_283_, lean_object* v_b_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_282_, v_as_x27_283_, v_b_284_, v___y_285_);
lean_dec_ref(v___y_285_);
lean_dec(v_as_x27_283_);
lean_dec(v___x_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_box(0);
return v___x_289_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v_fst_292_; uint8_t v___x_293_; 
v_head_290_ = lean_ctor_get(v_x_288_, 0);
v_tail_291_ = lean_ctor_get(v_x_288_, 1);
v_fst_292_ = lean_ctor_get(v_head_290_, 0);
v___x_293_ = l_Lean_isPrivateName(v_fst_292_);
if (v___x_293_ == 0)
{
v_x_288_ = v_tail_291_;
goto _start;
}
else
{
lean_object* v___x_295_; 
lean_inc(v_head_290_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_head_290_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_296_);
lean_dec(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_298_, lean_object* v_opt_299_){
_start:
{
lean_object* v_name_300_; lean_object* v_defValue_301_; lean_object* v_map_302_; lean_object* v___x_303_; 
v_name_300_ = lean_ctor_get(v_opt_299_, 0);
v_defValue_301_ = lean_ctor_get(v_opt_299_, 1);
v_map_302_ = lean_ctor_get(v_opts_298_, 0);
v___x_303_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_302_, v_name_300_);
if (lean_obj_tag(v___x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = lean_unbox(v_defValue_301_);
return v___x_304_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_303_, 1);
if (lean_obj_tag(v_val_305_) == 1)
{
uint8_t v_v_306_; 
v_v_306_ = lean_ctor_get_uint8(v_val_305_, 0);
lean_dec_ref_known(v_val_305_, 0);
return v_v_306_;
}
else
{
uint8_t v___x_307_; 
lean_dec(v_val_305_);
v___x_307_ = lean_unbox(v_defValue_301_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_308_, lean_object* v_opt_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_308_, v_opt_309_);
lean_dec_ref(v_opt_309_);
lean_dec_ref(v_opts_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_options_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_options_315_ = lean_ctor_get(v___y_313_, 2);
v___x_316_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_315_, v_opt_312_);
v___x_317_ = lean_box(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_319_, v___y_320_);
lean_dec_ref(v___y_320_);
lean_dec_ref(v_opt_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; lean_object* v_mctx_332_; lean_object* v_lctx_333_; lean_object* v_options_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_329_ = lean_st_ref_get(v___y_327_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
v___x_331_ = lean_st_ref_get(v___y_325_);
v_mctx_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc_ref(v_mctx_332_);
lean_dec(v___x_331_);
v_lctx_333_ = lean_ctor_get(v___y_324_, 2);
v_options_334_ = lean_ctor_get(v___y_326_, 2);
lean_inc_ref(v_options_334_);
lean_inc_ref(v_lctx_333_);
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_env_330_);
lean_ctor_set(v___x_335_, 1, v_mctx_332_);
lean_ctor_set(v___x_335_, 2, v_lctx_333_);
lean_ctor_set(v___x_335_, 3, v_options_334_);
v___x_336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_msgData_323_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v___y_352_, uint8_t v_suppressElabErrors_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 1)
{
lean_object* v_pre_355_; 
v_pre_355_ = lean_ctor_get(v_x_354_, 0);
switch(lean_obj_tag(v_pre_355_))
{
case 1:
{
lean_object* v_pre_356_; 
v_pre_356_ = lean_ctor_get(v_pre_355_, 0);
switch(lean_obj_tag(v_pre_356_))
{
case 0:
{
lean_object* v_str_357_; lean_object* v_str_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_str_357_ = lean_ctor_get(v_x_354_, 1);
v_str_358_ = lean_ctor_get(v_pre_355_, 1);
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_360_ = lean_string_dec_eq(v_str_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_362_ = lean_string_dec_eq(v_str_358_, v___x_361_);
if (v___x_362_ == 0)
{
return v___y_352_;
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_364_ = lean_string_dec_eq(v_str_357_, v___x_363_);
if (v___x_364_ == 0)
{
return v___y_352_;
}
else
{
return v_suppressElabErrors_353_;
}
}
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_366_ = lean_string_dec_eq(v_str_357_, v___x_365_);
if (v___x_366_ == 0)
{
return v___y_352_;
}
else
{
return v_suppressElabErrors_353_;
}
}
}
case 1:
{
lean_object* v_pre_367_; 
v_pre_367_ = lean_ctor_get(v_pre_356_, 0);
if (lean_obj_tag(v_pre_367_) == 0)
{
lean_object* v_str_368_; lean_object* v_str_369_; lean_object* v_str_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_str_368_ = lean_ctor_get(v_x_354_, 1);
v_str_369_ = lean_ctor_get(v_pre_355_, 1);
v_str_370_ = lean_ctor_get(v_pre_356_, 1);
v___x_371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_372_ = lean_string_dec_eq(v_str_370_, v___x_371_);
if (v___x_372_ == 0)
{
return v___y_352_;
}
else
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_374_ = lean_string_dec_eq(v_str_369_, v___x_373_);
if (v___x_374_ == 0)
{
return v___y_352_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_376_ = lean_string_dec_eq(v_str_368_, v___x_375_);
if (v___x_376_ == 0)
{
return v___y_352_;
}
else
{
return v_suppressElabErrors_353_;
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
lean_object* v_str_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_str_377_ = lean_ctor_get(v_x_354_, 1);
v___x_378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_379_ = lean_string_dec_eq(v_str_377_, v___x_378_);
if (v___x_379_ == 0)
{
return v___y_352_;
}
else
{
return v_suppressElabErrors_353_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v___y_380_, lean_object* v_suppressElabErrors_381_, lean_object* v_x_382_){
_start:
{
uint8_t v___y_39017__boxed_383_; uint8_t v_suppressElabErrors_boxed_384_; uint8_t v_res_385_; lean_object* v_r_386_; 
v___y_39017__boxed_383_ = lean_unbox(v___y_380_);
v_suppressElabErrors_boxed_384_ = lean_unbox(v_suppressElabErrors_381_);
v_res_385_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v___y_39017__boxed_383_, v_suppressElabErrors_boxed_384_, v_x_382_);
lean_dec(v_x_382_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_388_, lean_object* v_msgData_389_, uint8_t v_severity_390_, uint8_t v_isSilent_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___y_398_; uint8_t v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_434_; uint8_t v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; uint8_t v___y_465_; lean_object* v___y_466_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; uint8_t v___y_475_; uint8_t v___y_476_; uint8_t v___x_481_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; uint8_t v___y_489_; uint8_t v___y_491_; uint8_t v___x_506_; 
v___x_481_ = 2;
v___x_506_ = l_Lean_instBEqMessageSeverity_beq(v_severity_390_, v___x_481_);
if (v___x_506_ == 0)
{
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
else
{
uint8_t v___x_507_; 
lean_inc_ref(v_msgData_389_);
v___x_507_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_389_);
v___y_491_ = v___x_507_;
goto v___jp_490_;
}
v___jp_397_:
{
lean_object* v___x_407_; lean_object* v_currNamespace_408_; lean_object* v_openDecls_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_cache_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_432_; 
v___x_407_ = lean_st_ref_take(v___y_406_);
v_currNamespace_408_ = lean_ctor_get(v___y_405_, 6);
v_openDecls_409_ = lean_ctor_get(v___y_405_, 7);
v_env_410_ = lean_ctor_get(v___x_407_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_407_, 1);
v_ngen_412_ = lean_ctor_get(v___x_407_, 2);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_407_, 3);
v_traceState_414_ = lean_ctor_get(v___x_407_, 4);
v_cache_415_ = lean_ctor_get(v___x_407_, 5);
v_messages_416_ = lean_ctor_get(v___x_407_, 6);
v_infoState_417_ = lean_ctor_get(v___x_407_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_407_, 8);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_432_ == 0)
{
v___x_420_ = v___x_407_;
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_openDecls_409_);
lean_inc(v_currNamespace_408_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_currNamespace_408_);
lean_ctor_set(v___x_422_, 1, v_openDecls_409_);
v___x_423_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___y_402_);
lean_inc_ref(v___y_398_);
lean_inc_ref(v___y_401_);
v___x_424_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_424_, 0, v___y_401_);
lean_ctor_set(v___x_424_, 1, v___y_404_);
lean_ctor_set(v___x_424_, 2, v___y_403_);
lean_ctor_set(v___x_424_, 3, v___y_398_);
lean_ctor_set(v___x_424_, 4, v___x_423_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*5, v___y_399_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*5 + 1, v___y_400_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*5 + 2, v_isSilent_391_);
v___x_425_ = l_Lean_MessageLog_add(v___x_424_, v_messages_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 6, v___x_425_);
v___x_427_ = v___x_420_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_snapshotTasks_418_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_st_ref_set(v___y_406_, v___x_427_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
v___jp_433_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_457_; 
v___x_442_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_389_);
v___x_443_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_442_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_457_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc_ref_n(v___y_437_, 2);
v___x_448_ = l_Lean_FileMap_toPosition(v___y_437_, v___y_436_);
lean_dec(v___y_436_);
v___x_449_ = l_Lean_FileMap_toPosition(v___y_437_, v___y_441_);
lean_dec(v___y_441_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_440_ == 0)
{
lean_del_object(v___x_446_);
lean_dec_ref(v___y_434_);
v___y_398_ = v___x_451_;
v___y_399_ = v___y_435_;
v___y_400_ = v___y_439_;
v___y_401_ = v___y_438_;
v___y_402_ = v_a_444_;
v___y_403_ = v___x_450_;
v___y_404_ = v___x_448_;
v___y_405_ = v___y_394_;
v___y_406_ = v___y_395_;
goto v___jp_397_;
}
else
{
uint8_t v___x_452_; 
lean_inc(v_a_444_);
v___x_452_ = l_Lean_MessageData_hasTag(v___y_434_, v_a_444_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref_known(v___x_450_, 1);
lean_dec_ref(v___x_448_);
lean_dec(v_a_444_);
v___x_453_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_453_);
v___x_455_ = v___x_446_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_del_object(v___x_446_);
v___y_398_ = v___x_451_;
v___y_399_ = v___y_435_;
v___y_400_ = v___y_439_;
v___y_401_ = v___y_438_;
v___y_402_ = v_a_444_;
v___y_403_ = v___x_450_;
v___y_404_ = v___x_448_;
v___y_405_ = v___y_394_;
v___y_406_ = v___y_395_;
goto v___jp_397_;
}
}
}
}
v___jp_458_:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Syntax_getTailPos_x3f(v___y_464_, v___y_460_);
lean_dec(v___y_464_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_inc(v___y_466_);
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_466_;
v___y_437_ = v___y_461_;
v___y_438_ = v___y_463_;
v___y_439_ = v___y_462_;
v___y_440_ = v___y_465_;
v___y_441_ = v___y_466_;
goto v___jp_433_;
}
else
{
lean_object* v_val_468_; 
v_val_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_467_, 1);
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_466_;
v___y_437_ = v___y_461_;
v___y_438_ = v___y_463_;
v___y_439_ = v___y_462_;
v___y_440_ = v___y_465_;
v___y_441_ = v_val_468_;
goto v___jp_433_;
}
}
v___jp_469_:
{
lean_object* v_ref_477_; lean_object* v___x_478_; 
v_ref_477_ = l_Lean_replaceRef(v_ref_388_, v___y_473_);
v___x_478_ = l_Lean_Syntax_getPos_x3f(v_ref_477_, v___y_471_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___y_459_ = v___y_470_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_472_;
v___y_462_ = v___y_476_;
v___y_463_ = v___y_474_;
v___y_464_ = v_ref_477_;
v___y_465_ = v___y_475_;
v___y_466_ = v___x_479_;
goto v___jp_458_;
}
else
{
lean_object* v_val_480_; 
v_val_480_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v___x_478_, 1);
v___y_459_ = v___y_470_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_472_;
v___y_462_ = v___y_476_;
v___y_463_ = v___y_474_;
v___y_464_ = v_ref_477_;
v___y_465_ = v___y_475_;
v___y_466_ = v_val_480_;
goto v___jp_458_;
}
}
v___jp_482_:
{
if (v___y_489_ == 0)
{
v___y_470_ = v___y_486_;
v___y_471_ = v___y_488_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_484_;
v___y_474_ = v___y_485_;
v___y_475_ = v___y_487_;
v___y_476_ = v_severity_390_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___y_486_;
v___y_471_ = v___y_488_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_484_;
v___y_474_ = v___y_485_;
v___y_475_ = v___y_487_;
v___y_476_ = v___x_481_;
goto v___jp_469_;
}
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_object* v_fileName_492_; lean_object* v_fileMap_493_; lean_object* v_options_494_; lean_object* v_ref_495_; uint8_t v_suppressElabErrors_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___f_499_; uint8_t v___x_500_; uint8_t v___x_501_; 
v_fileName_492_ = lean_ctor_get(v___y_394_, 0);
v_fileMap_493_ = lean_ctor_get(v___y_394_, 1);
v_options_494_ = lean_ctor_get(v___y_394_, 2);
v_ref_495_ = lean_ctor_get(v___y_394_, 5);
v_suppressElabErrors_496_ = lean_ctor_get_uint8(v___y_394_, sizeof(void*)*14 + 1);
v___x_497_ = lean_box(v___y_491_);
v___x_498_ = lean_box(v_suppressElabErrors_496_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_499_, 0, v___x_497_);
lean_closure_set(v___f_499_, 1, v___x_498_);
v___x_500_ = 1;
v___x_501_ = l_Lean_instBEqMessageSeverity_beq(v_severity_390_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_483_ = v_fileMap_493_;
v___y_484_ = v_ref_495_;
v___y_485_ = v_fileName_492_;
v___y_486_ = v___f_499_;
v___y_487_ = v_suppressElabErrors_496_;
v___y_488_ = v___y_491_;
v___y_489_ = v___x_501_;
goto v___jp_482_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = l_Lean_warningAsError;
v___x_503_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_494_, v___x_502_);
v___y_483_ = v_fileMap_493_;
v___y_484_ = v_ref_495_;
v___y_485_ = v_fileName_492_;
v___y_486_ = v___f_499_;
v___y_487_ = v_suppressElabErrors_496_;
v___y_488_ = v___y_491_;
v___y_489_ = v___x_503_;
goto v___jp_482_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_msgData_389_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_508_, lean_object* v_msgData_509_, lean_object* v_severity_510_, lean_object* v_isSilent_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v_severity_boxed_517_; uint8_t v_isSilent_boxed_518_; lean_object* v_res_519_; 
v_severity_boxed_517_ = lean_unbox(v_severity_510_);
v_isSilent_boxed_518_ = lean_unbox(v_isSilent_511_);
v_res_519_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_508_, v_msgData_509_, v_severity_boxed_517_, v_isSilent_boxed_518_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v_ref_508_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_520_, uint8_t v_severity_521_, uint8_t v_isSilent_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_ref_532_; lean_object* v___x_533_; 
v_ref_532_ = lean_ctor_get(v___y_529_, 5);
v___x_533_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_532_, v_msgData_520_, v_severity_521_, v_isSilent_522_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_534_, lean_object* v_severity_535_, lean_object* v_isSilent_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v_severity_boxed_546_; uint8_t v_isSilent_boxed_547_; lean_object* v_res_548_; 
v_severity_boxed_546_ = lean_unbox(v_severity_535_);
v_isSilent_boxed_547_ = lean_unbox(v_isSilent_536_);
v_res_548_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_534_, v_severity_boxed_546_, v_isSilent_boxed_547_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = 1;
v___x_560_ = 0;
v___x_561_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_549_, v___x_559_, v___x_560_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_612_; 
v___x_589_ = lean_st_ref_get(v___y_587_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_591_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_591_, v___y_586_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v_isExporting_602_; 
v_isExporting_602_ = lean_ctor_get_uint8(v_env_590_, sizeof(void*)*8);
lean_dec_ref(v_env_590_);
if (v_isExporting_602_ == 0)
{
lean_dec(v_a_593_);
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_isPrivateName(v_id_579_);
if (v___x_603_ == 0)
{
lean_dec(v_a_593_);
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_604_ == 0)
{
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_595_);
v___x_605_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_606_ = 0;
v___x_607_ = l_Lean_MessageData_ofConstName(v_id_579_, v___x_606_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_610_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_611_;
}
}
}
v___jp_597_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_box(0);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_624_, uint8_t v_enableLog_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_env_636_; lean_object* v_options_637_; lean_object* v_currNamespace_638_; lean_object* v_openDecls_639_; lean_object* v___x_640_; lean_object* v_env_641_; lean_object* v_res_642_; 
v___x_635_ = lean_st_ref_get(v___y_633_);
v_env_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_635_);
v_options_637_ = lean_ctor_get(v___y_632_, 2);
v_currNamespace_638_ = lean_ctor_get(v___y_632_, 6);
v_openDecls_639_ = lean_ctor_get(v___y_632_, 7);
v___x_640_ = lean_st_ref_get(v___y_633_);
v_env_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_env_641_);
lean_dec(v___x_640_);
lean_inc(v_openDecls_639_);
lean_inc(v_currNamespace_638_);
v_res_642_ = l_Lean_ResolveName_resolveGlobalName(v_env_636_, v_options_637_, v_currNamespace_638_, v_openDecls_639_, v_id_624_);
if (v_enableLog_625_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_env_641_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_res_642_);
return v___x_643_;
}
else
{
uint8_t v_isExporting_644_; 
v_isExporting_644_ = lean_ctor_get_uint8(v_env_641_, sizeof(void*)*8);
lean_dec_ref(v_env_641_);
if (v_isExporting_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_res_642_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_642_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; lean_object* v_fst_648_; lean_object* v___x_649_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
v_fst_648_ = lean_ctor_get(v_val_647_, 0);
lean_inc(v_fst_648_);
lean_dec(v_val_647_);
v___x_649_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_648_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_657_);
v___x_651_ = v___x_649_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_dec(v___x_649_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_res_642_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_res_642_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_res_642_);
v_a_658_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_649_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_649_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v___x_666_; 
lean_dec(v___x_646_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_res_642_);
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_667_, lean_object* v_enableLog_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v_enableLog_boxed_678_; lean_object* v_res_679_; 
v_enableLog_boxed_678_ = lean_unbox(v_enableLog_668_);
v_res_679_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_667_, v_enableLog_boxed_678_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_680_, lean_object* v_a_681_){
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
lean_object* v_head_683_; lean_object* v_tail_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v_head_683_ = lean_ctor_get(v_a_680_, 0);
v_tail_684_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_695_ == 0)
{
v___x_686_ = v_a_680_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_tail_684_);
lean_inc(v_head_683_);
lean_dec(v_a_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_snd_688_; uint8_t v___x_689_; 
v_snd_688_ = lean_ctor_get(v_head_683_, 1);
v___x_689_ = l_List_isEmpty___redArg(v_snd_688_);
if (v___x_689_ == 0)
{
lean_del_object(v___x_686_);
lean_dec(v_head_683_);
v_a_680_ = v_tail_684_;
goto _start;
}
else
{
lean_object* v___x_692_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_a_681_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_head_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_681_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_a_680_ = v_tail_684_;
v_a_681_ = v___x_692_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
if (lean_obj_tag(v_a_696_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l_List_reverse___redArg(v_a_697_);
return v___x_698_;
}
else
{
lean_object* v_head_699_; lean_object* v_tail_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
v_head_699_ = lean_ctor_get(v_a_696_, 0);
v_tail_700_ = lean_ctor_get(v_a_696_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_709_ == 0)
{
v___x_702_ = v_a_696_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_tail_700_);
lean_inc(v_head_699_);
lean_dec(v_a_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v___x_706_; 
v_fst_704_ = lean_ctor_get(v_head_699_, 0);
lean_inc(v_fst_704_);
lean_dec(v_head_699_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_a_697_);
lean_ctor_set(v___x_702_, 0, v_fst_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_a_697_);
v___x_706_ = v_reuseFailAlloc_708_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_a_696_ = v_tail_700_;
v_a_697_ = v___x_706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_ref_716_; lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_ref_716_ = lean_ctor_get(v___y_713_, 5);
v___x_717_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc(v_ref_716_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_ref_716_);
lean_ctor_set(v___x_722_, 1, v_a_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_fileName_745_; lean_object* v_fileMap_746_; lean_object* v_options_747_; lean_object* v_currRecDepth_748_; lean_object* v_maxRecDepth_749_; lean_object* v_ref_750_; lean_object* v_currNamespace_751_; lean_object* v_openDecls_752_; lean_object* v_initHeartbeats_753_; lean_object* v_maxHeartbeats_754_; lean_object* v_quotContext_755_; lean_object* v_currMacroScope_756_; uint8_t v_diag_757_; lean_object* v_cancelTk_x3f_758_; uint8_t v_suppressElabErrors_759_; lean_object* v_inheritedTraceOptions_760_; lean_object* v_ref_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_fileName_745_ = lean_ctor_get(v___y_742_, 0);
v_fileMap_746_ = lean_ctor_get(v___y_742_, 1);
v_options_747_ = lean_ctor_get(v___y_742_, 2);
v_currRecDepth_748_ = lean_ctor_get(v___y_742_, 3);
v_maxRecDepth_749_ = lean_ctor_get(v___y_742_, 4);
v_ref_750_ = lean_ctor_get(v___y_742_, 5);
v_currNamespace_751_ = lean_ctor_get(v___y_742_, 6);
v_openDecls_752_ = lean_ctor_get(v___y_742_, 7);
v_initHeartbeats_753_ = lean_ctor_get(v___y_742_, 8);
v_maxHeartbeats_754_ = lean_ctor_get(v___y_742_, 9);
v_quotContext_755_ = lean_ctor_get(v___y_742_, 10);
v_currMacroScope_756_ = lean_ctor_get(v___y_742_, 11);
v_diag_757_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*14);
v_cancelTk_x3f_758_ = lean_ctor_get(v___y_742_, 12);
v_suppressElabErrors_759_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_760_ = lean_ctor_get(v___y_742_, 13);
v_ref_761_ = l_Lean_replaceRef(v_ref_734_, v_ref_750_);
lean_inc_ref(v_inheritedTraceOptions_760_);
lean_inc(v_cancelTk_x3f_758_);
lean_inc(v_currMacroScope_756_);
lean_inc(v_quotContext_755_);
lean_inc(v_maxHeartbeats_754_);
lean_inc(v_initHeartbeats_753_);
lean_inc(v_openDecls_752_);
lean_inc(v_currNamespace_751_);
lean_inc(v_maxRecDepth_749_);
lean_inc(v_currRecDepth_748_);
lean_inc_ref(v_options_747_);
lean_inc_ref(v_fileMap_746_);
lean_inc_ref(v_fileName_745_);
v___x_762_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_762_, 0, v_fileName_745_);
lean_ctor_set(v___x_762_, 1, v_fileMap_746_);
lean_ctor_set(v___x_762_, 2, v_options_747_);
lean_ctor_set(v___x_762_, 3, v_currRecDepth_748_);
lean_ctor_set(v___x_762_, 4, v_maxRecDepth_749_);
lean_ctor_set(v___x_762_, 5, v_ref_761_);
lean_ctor_set(v___x_762_, 6, v_currNamespace_751_);
lean_ctor_set(v___x_762_, 7, v_openDecls_752_);
lean_ctor_set(v___x_762_, 8, v_initHeartbeats_753_);
lean_ctor_set(v___x_762_, 9, v_maxHeartbeats_754_);
lean_ctor_set(v___x_762_, 10, v_quotContext_755_);
lean_ctor_set(v___x_762_, 11, v_currMacroScope_756_);
lean_ctor_set(v___x_762_, 12, v_cancelTk_x3f_758_);
lean_ctor_set(v___x_762_, 13, v_inheritedTraceOptions_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*14, v_diag_757_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*14 + 1, v_suppressElabErrors_759_);
v___x_763_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_735_, v___y_740_, v___y_741_, v___x_762_, v___y_743_);
lean_dec_ref_known(v___x_762_, 14);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_764_, lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_764_, v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v_ref_764_);
return v_res_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_ctor_set(v___x_781_, 3, v___x_780_);
lean_ctor_set(v___x_781_, 4, v___x_779_);
lean_ctor_set(v___x_781_, 5, v___x_779_);
lean_ctor_set(v___x_781_, 6, v___x_779_);
lean_ctor_set(v___x_781_, 7, v___x_779_);
lean_ctor_set(v___x_781_, 8, v___x_779_);
lean_ctor_set(v___x_781_, 9, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(32u);
v___x_783_ = lean_mk_empty_array_with_capacity(v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_785_ = ((size_t)5ULL);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_unsigned_to_nat(32u);
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_787_);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_790_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
lean_ctor_set(v___x_790_, 2, v___x_786_);
lean_ctor_set(v___x_790_, 3, v___x_786_);
lean_ctor_set_usize(v___x_790_, 4, v___x_785_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_box(1);
v___x_792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
lean_ctor_set(v___x_794_, 2, v___x_791_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_816_, lean_object* v_declHint_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_env_821_; uint8_t v___y_823_; uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_820_ = lean_st_ref_get(v___y_818_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_env_821_);
lean_dec(v___x_820_);
v___x_879_ = l_Lean_Name_isAnonymous(v_declHint_817_);
v___x_880_ = lean_bool_not(v___x_879_);
if (v___x_880_ == 0)
{
v___y_823_ = v___x_880_;
goto v___jp_822_;
}
else
{
uint8_t v_isExporting_881_; 
v_isExporting_881_ = lean_ctor_get_uint8(v_env_821_, sizeof(void*)*8);
v___y_823_ = v_isExporting_881_;
goto v___jp_822_;
}
v___jp_822_:
{
if (v___y_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v_env_821_);
lean_dec(v_declHint_817_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v_msg_816_);
return v___x_824_;
}
else
{
uint8_t v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = 0;
lean_inc_ref(v_env_821_);
v___x_826_ = l_Lean_Environment_setExporting(v_env_821_, v___x_825_);
lean_inc(v_declHint_817_);
lean_inc_ref(v___x_826_);
v___x_827_ = l_Lean_Environment_contains(v___x_826_, v_declHint_817_, v___y_823_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v___x_826_);
lean_dec_ref(v_env_821_);
lean_dec(v_declHint_817_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_msg_816_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_c_834_; lean_object* v___x_835_; 
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_831_ = l_Lean_Options_empty;
v___x_832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_832_, 0, v___x_826_);
lean_ctor_set(v___x_832_, 1, v___x_829_);
lean_ctor_set(v___x_832_, 2, v___x_830_);
lean_ctor_set(v___x_832_, 3, v___x_831_);
lean_inc(v_declHint_817_);
v___x_833_ = l_Lean_MessageData_ofConstName(v_declHint_817_, v___x_825_);
v_c_834_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_834_, 0, v___x_832_);
lean_ctor_set(v_c_834_, 1, v___x_833_);
v___x_835_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_821_, v_declHint_817_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_env_821_);
lean_dec(v_declHint_817_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_c_834_);
v___x_838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_MessageData_note(v___x_839_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v_msg_816_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_878_; 
v_val_843_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_878_ == 0)
{
v___x_845_ = v___x_835_;
v_isShared_846_ = v_isSharedCheck_878_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v___x_835_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_878_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_mod_850_; uint8_t v___x_851_; 
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_Environment_header(v_env_821_);
lean_dec_ref(v_env_821_);
v___x_849_ = l_Lean_EnvironmentHeader_moduleNames(v___x_848_);
v_mod_850_ = lean_array_get(v___x_847_, v___x_849_, v_val_843_);
lean_dec(v_val_843_);
lean_dec_ref(v___x_849_);
v___x_851_ = l_Lean_isPrivateName(v_declHint_817_);
lean_dec(v_declHint_817_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_c_834_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_ofName(v_mod_850_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Lean_MessageData_note(v___x_859_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v_msg_816_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_861_);
v___x_863_ = v___x_845_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v_c_834_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_ofName(v_mod_850_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MessageData_note(v___x_872_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v_msg_816_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_874_);
v___x_876_ = v___x_845_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_882_, v_declHint_883_, v___y_884_);
lean_dec(v___y_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_887_, lean_object* v_declHint_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
v___x_898_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_887_, v_declHint_888_, v___y_896_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_908_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_903_ = l_Lean_unknownIdentifierMessageTag;
v___x_904_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_a_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_909_, lean_object* v_declHint_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_909_, v_declHint_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_921_, lean_object* v_msg_922_, lean_object* v_declHint_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_a_934_; lean_object* v___x_935_; 
v___x_933_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_922_, v_declHint_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_921_, v_a_934_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_936_, lean_object* v_msg_937_, lean_object* v_declHint_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_936_, v_msg_937_, v_declHint_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v_ref_936_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_955_, lean_object* v_constName_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_966_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_967_ = 0;
lean_inc(v_constName_956_);
v___x_968_ = l_Lean_MessageData_ofConstName(v_constName_956_, v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_955_, v___x_971_, v_constName_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_973_, lean_object* v_constName_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_973_, v_constName_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v_ref_973_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_985_, lean_object* v_cs_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_cs_997_; uint8_t v___x_1001_; 
v___x_996_ = lean_box(0);
v_cs_997_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_986_, v___x_996_);
v___x_1001_ = l_List_isEmpty___redArg(v_cs_997_);
if (v___x_1001_ == 0)
{
lean_dec(v_n_985_);
goto v___jp_998_;
}
else
{
lean_object* v_ref_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_cs_997_);
v_ref_1002_ = lean_ctor_get(v___y_993_, 5);
v___x_1003_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_1002_, v_n_985_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
v___jp_998_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_997_, v___x_996_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1012_, lean_object* v_cs_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1012_, v_cs_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = 1;
lean_inc(v_n_1024_);
v___x_1035_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1024_, v___x_1034_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1024_, v_a_1036_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1037_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_n_1024_);
v_a_1038_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1035_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1035_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
if (lean_obj_tag(v_a_1057_) == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_array_to_list(v_a_1058_);
return v___x_1059_;
}
else
{
lean_object* v_head_1060_; 
v_head_1060_ = lean_ctor_get(v_a_1057_, 0);
if (lean_obj_tag(v_head_1060_) == 1)
{
lean_object* v_fields_1061_; 
v_fields_1061_ = lean_ctor_get(v_head_1060_, 1);
if (lean_obj_tag(v_fields_1061_) == 0)
{
lean_object* v_tail_1062_; lean_object* v_n_1063_; lean_object* v___x_1064_; 
lean_inc_ref(v_head_1060_);
v_tail_1062_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_tail_1062_);
lean_dec_ref_known(v_a_1057_, 2);
v_n_1063_ = lean_ctor_get(v_head_1060_, 0);
lean_inc(v_n_1063_);
lean_dec_ref_known(v_head_1060_, 2);
v___x_1064_ = lean_array_push(v_a_1058_, v_n_1063_);
v_a_1057_ = v_tail_1062_;
v_a_1058_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v_tail_1066_; 
v_tail_1066_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_tail_1066_);
lean_dec_ref_known(v_a_1057_, 2);
v_a_1057_ = v_tail_1066_;
goto _start;
}
}
else
{
lean_object* v_tail_1068_; 
v_tail_1068_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_tail_1068_);
lean_dec_ref_known(v_a_1057_, 2);
v_a_1057_ = v_tail_1068_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1076_ = l_Lean_MessageData_ofFormat(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1077_, lean_object* v_k_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
if (lean_obj_tag(v_stx_1077_) == 3)
{
lean_object* v_val_1088_; lean_object* v_preresolved_1089_; lean_object* v___x_1090_; lean_object* v_pre_1091_; uint8_t v___x_1092_; 
v_val_1088_ = lean_ctor_get(v_stx_1077_, 2);
lean_inc(v_val_1088_);
v_preresolved_1089_ = lean_ctor_get(v_stx_1077_, 3);
v___x_1090_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1089_);
v_pre_1091_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1089_, v___x_1090_);
v___x_1092_ = l_List_isEmpty___redArg(v_pre_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref_known(v_stx_1077_, 4);
lean_dec(v_val_1088_);
lean_dec_ref(v_k_1078_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_pre_1091_);
return v___x_1093_;
}
else
{
lean_object* v_fileName_1094_; lean_object* v_fileMap_1095_; lean_object* v_options_1096_; lean_object* v_currRecDepth_1097_; lean_object* v_maxRecDepth_1098_; lean_object* v_ref_1099_; lean_object* v_currNamespace_1100_; lean_object* v_openDecls_1101_; lean_object* v_initHeartbeats_1102_; lean_object* v_maxHeartbeats_1103_; lean_object* v_quotContext_1104_; lean_object* v_currMacroScope_1105_; uint8_t v_diag_1106_; lean_object* v_cancelTk_x3f_1107_; uint8_t v_suppressElabErrors_1108_; lean_object* v_inheritedTraceOptions_1109_; lean_object* v_ref_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_pre_1091_);
v_fileName_1094_ = lean_ctor_get(v___y_1085_, 0);
v_fileMap_1095_ = lean_ctor_get(v___y_1085_, 1);
v_options_1096_ = lean_ctor_get(v___y_1085_, 2);
v_currRecDepth_1097_ = lean_ctor_get(v___y_1085_, 3);
v_maxRecDepth_1098_ = lean_ctor_get(v___y_1085_, 4);
v_ref_1099_ = lean_ctor_get(v___y_1085_, 5);
v_currNamespace_1100_ = lean_ctor_get(v___y_1085_, 6);
v_openDecls_1101_ = lean_ctor_get(v___y_1085_, 7);
v_initHeartbeats_1102_ = lean_ctor_get(v___y_1085_, 8);
v_maxHeartbeats_1103_ = lean_ctor_get(v___y_1085_, 9);
v_quotContext_1104_ = lean_ctor_get(v___y_1085_, 10);
v_currMacroScope_1105_ = lean_ctor_get(v___y_1085_, 11);
v_diag_1106_ = lean_ctor_get_uint8(v___y_1085_, sizeof(void*)*14);
v_cancelTk_x3f_1107_ = lean_ctor_get(v___y_1085_, 12);
v_suppressElabErrors_1108_ = lean_ctor_get_uint8(v___y_1085_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1109_ = lean_ctor_get(v___y_1085_, 13);
v_ref_1110_ = l_Lean_replaceRef(v_stx_1077_, v_ref_1099_);
lean_dec_ref_known(v_stx_1077_, 4);
lean_inc_ref(v_inheritedTraceOptions_1109_);
lean_inc(v_cancelTk_x3f_1107_);
lean_inc(v_currMacroScope_1105_);
lean_inc(v_quotContext_1104_);
lean_inc(v_maxHeartbeats_1103_);
lean_inc(v_initHeartbeats_1102_);
lean_inc(v_openDecls_1101_);
lean_inc(v_currNamespace_1100_);
lean_inc(v_maxRecDepth_1098_);
lean_inc(v_currRecDepth_1097_);
lean_inc_ref(v_options_1096_);
lean_inc_ref(v_fileMap_1095_);
lean_inc_ref(v_fileName_1094_);
v___x_1111_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1111_, 0, v_fileName_1094_);
lean_ctor_set(v___x_1111_, 1, v_fileMap_1095_);
lean_ctor_set(v___x_1111_, 2, v_options_1096_);
lean_ctor_set(v___x_1111_, 3, v_currRecDepth_1097_);
lean_ctor_set(v___x_1111_, 4, v_maxRecDepth_1098_);
lean_ctor_set(v___x_1111_, 5, v_ref_1110_);
lean_ctor_set(v___x_1111_, 6, v_currNamespace_1100_);
lean_ctor_set(v___x_1111_, 7, v_openDecls_1101_);
lean_ctor_set(v___x_1111_, 8, v_initHeartbeats_1102_);
lean_ctor_set(v___x_1111_, 9, v_maxHeartbeats_1103_);
lean_ctor_set(v___x_1111_, 10, v_quotContext_1104_);
lean_ctor_set(v___x_1111_, 11, v_currMacroScope_1105_);
lean_ctor_set(v___x_1111_, 12, v_cancelTk_x3f_1107_);
lean_ctor_set(v___x_1111_, 13, v_inheritedTraceOptions_1109_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*14, v_diag_1106_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*14 + 1, v_suppressElabErrors_1108_);
lean_inc(v___y_1086_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
v___x_1112_ = lean_apply_10(v_k_1078_, v_val_1088_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___x_1111_, v___y_1086_, lean_box(0));
return v___x_1112_;
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_k_1078_);
v___x_1113_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1114_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1077_, v___x_1113_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_stx_1077_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1115_, lean_object* v_k_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1115_, v_k_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1139_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1128_, v___x_1138_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1151_, size_t v_sz_1152_, size_t v_i_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_lt(v_i_1153_, v_sz_1152_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_b_1154_);
return v___x_1165_;
}
else
{
lean_object* v_a_1166_; lean_object* v_name_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_a_1166_ = lean_array_uget_borrowed(v_as_1151_, v_i_1153_);
v_name_1167_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_name_1167_);
v___x_1168_ = l_Lean_mkIdent(v_name_1167_);
lean_inc(v___x_1168_);
v___x_1169_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1168_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1168_, v_a_1170_, v_b_1154_, v___y_1161_);
lean_dec(v_a_1170_);
lean_dec(v___x_1168_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; size_t v___x_1173_; size_t v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1153_, v___x_1173_);
v_i_1153_ = v___x_1174_;
v_b_1154_ = v_a_1172_;
goto _start;
}
else
{
return v___x_1171_;
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v___x_1168_);
lean_dec_ref(v_b_1154_);
v_a_1176_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1169_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1169_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1184_, lean_object* v_sz_1185_, lean_object* v_i_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1185_);
lean_dec(v_sz_1185_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1184_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_as_1184_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1219_, lean_object* v_stx_1220_, uint8_t v___x_1221_, lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v___f_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
if (v___x_1219_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_1235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v_tk_1237_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1309_; uint8_t v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___y_1313_; lean_object* v_stxForSuggestion_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; uint8_t v___y_1383_; lean_object* v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; uint8_t v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; uint8_t v___y_1558_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; lean_object* v_stxForExecution_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; uint8_t v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; uint8_t v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; uint8_t v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; uint8_t v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; uint8_t v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; uint8_t v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v_argsArray_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; uint8_t v___y_1931_; lean_object* v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v_args_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___x_2035_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; uint8_t v___y_2041_; lean_object* v_o_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v_bang_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v_tk_1237_ = l_Lean_Syntax_getArg(v_stx_1220_, v___x_1236_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_Syntax_getArg(v_stx_1220_, v___x_2035_);
v___x_2095_ = l_Lean_Syntax_isNone(v___x_2094_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
lean_inc(v___x_2094_);
v___x_2096_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_2035_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec(v___x_2094_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2097_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2097_;
}
else
{
lean_object* v_bang_2098_; lean_object* v___x_2099_; 
v_bang_2098_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_1236_);
lean_dec(v___x_2094_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_bang_2098_);
v_bang_2066_ = v___x_2099_;
v___y_2067_ = v___y_1226_;
v___y_2068_ = v___y_1227_;
v___y_2069_ = v___y_1228_;
v___y_2070_ = v___y_1229_;
v___y_2071_ = v___y_1230_;
v___y_2072_ = v___y_1231_;
v___y_2073_ = v___y_1232_;
v___y_2074_ = v___y_1233_;
goto v___jp_2065_;
}
}
else
{
lean_object* v___x_2100_; 
lean_dec(v___x_2094_);
v___x_2100_ = lean_box(0);
v_bang_2066_ = v___x_2100_;
v___y_2067_ = v___y_1226_;
v___y_2068_ = v___y_1227_;
v___y_2069_ = v___y_1228_;
v___y_2070_ = v___y_1229_;
v___y_2071_ = v___y_1230_;
v___y_2072_ = v___y_1231_;
v___y_2073_ = v___y_1232_;
v___y_2074_ = v___y_1233_;
goto v___jp_2065_;
}
v___jp_1238_:
{
lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_box(v___x_1221_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1253_, 0, v___y_1240_);
lean_closure_set(v___f_1253_, 1, v___x_1236_);
lean_closure_set(v___f_1253_, 2, v___x_1252_);
lean_closure_set(v___f_1253_, 3, v___y_1251_);
lean_closure_set(v___f_1253_, 4, v___y_1241_);
v___x_1254_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1239_, v___f_1253_, v___y_1246_, v___y_1245_, v___y_1250_, v___y_1247_, v___y_1243_, v___y_1248_, v___y_1244_, v___y_1242_);
lean_dec(v___y_1239_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_usedTheorems_1256_; lean_object* v_diag_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1299_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_usedTheorems_1256_ = lean_ctor_get(v_a_1255_, 0);
v_diag_1257_ = lean_ctor_get(v_a_1255_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1259_ = v_a_1255_;
v_isShared_1260_ = v_isSharedCheck_1299_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_diag_1257_);
lean_inc(v_usedTheorems_1256_);
lean_dec(v_a_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1299_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1249_, v_usedTheorems_1256_, v___y_1243_, v___y_1248_, v___y_1244_, v___y_1242_);
lean_dec_ref(v_usedTheorems_1256_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_ref_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v_ref_1263_ = lean_ctor_get(v___y_1244_, 5);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_a_1262_);
lean_ctor_set(v___x_1259_, 0, v___x_1264_);
v___x_1266_ = v___x_1259_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1262_);
v___x_1266_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
lean_ctor_set(v___x_1268_, 3, v___x_1267_);
lean_ctor_set(v___x_1268_, 4, v___x_1267_);
lean_ctor_set(v___x_1268_, 5, v___x_1267_);
lean_inc(v_ref_1263_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_ref_1263_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1271_ = 4;
v___x_1272_ = l_Lean_MessageData_nil;
v___x_1273_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1237_, v___x_1268_, v___x_1269_, v___x_1270_, v___x_1267_, v___x_1271_, v___x_1272_, v___y_1244_, v___y_1242_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1281_);
v___x_1275_ = v___x_1273_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v_diag_1257_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_diag_1257_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_diag_1257_);
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_del_object(v___x_1259_);
lean_dec_ref(v_diag_1257_);
lean_dec(v_tk_1237_);
v_a_1291_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1261_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1261_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v___y_1249_);
lean_dec(v_tk_1237_);
v_a_1300_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1254_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1254_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
v___jp_1308_:
{
uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = 0;
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1325_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1311_, v___x_1323_, v___y_1310_, v___x_1323_, v___x_1324_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1311_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
if (lean_obj_tag(v___y_1312_) == 0)
{
lean_object* v_ctx_1327_; lean_object* v_simprocs_1328_; lean_object* v_dischargeWrapper_1329_; 
v_ctx_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_ctx_1327_);
v_simprocs_1328_ = lean_ctor_get(v_a_1326_, 1);
lean_inc_ref(v_simprocs_1328_);
v_dischargeWrapper_1329_ = lean_ctor_get(v_a_1326_, 2);
lean_inc(v_dischargeWrapper_1329_);
lean_dec(v_a_1326_);
v___y_1239_ = v_dischargeWrapper_1329_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v_simprocs_1328_;
v___y_1242_ = v___y_1322_;
v___y_1243_ = v___y_1319_;
v___y_1244_ = v___y_1321_;
v___y_1245_ = v___y_1316_;
v___y_1246_ = v___y_1315_;
v___y_1247_ = v___y_1318_;
v___y_1248_ = v___y_1320_;
v___y_1249_ = v_stxForSuggestion_1314_;
v___y_1250_ = v___y_1317_;
v___y_1251_ = v_ctx_1327_;
goto v___jp_1238_;
}
else
{
lean_dec_ref_known(v___y_1312_, 1);
if (v___y_1313_ == 0)
{
lean_object* v_ctx_1330_; lean_object* v_simprocs_1331_; lean_object* v_dischargeWrapper_1332_; 
v_ctx_1330_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_ctx_1330_);
v_simprocs_1331_ = lean_ctor_get(v_a_1326_, 1);
lean_inc_ref(v_simprocs_1331_);
v_dischargeWrapper_1332_ = lean_ctor_get(v_a_1326_, 2);
lean_inc(v_dischargeWrapper_1332_);
lean_dec(v_a_1326_);
v___y_1239_ = v_dischargeWrapper_1332_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v_simprocs_1331_;
v___y_1242_ = v___y_1322_;
v___y_1243_ = v___y_1319_;
v___y_1244_ = v___y_1321_;
v___y_1245_ = v___y_1316_;
v___y_1246_ = v___y_1315_;
v___y_1247_ = v___y_1318_;
v___y_1248_ = v___y_1320_;
v___y_1249_ = v_stxForSuggestion_1314_;
v___y_1250_ = v___y_1317_;
v___y_1251_ = v_ctx_1330_;
goto v___jp_1238_;
}
else
{
lean_object* v_ctx_1333_; lean_object* v_simprocs_1334_; lean_object* v_dischargeWrapper_1335_; lean_object* v___x_1336_; 
v_ctx_1333_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_ctx_1333_);
v_simprocs_1334_ = lean_ctor_get(v_a_1326_, 1);
lean_inc_ref(v_simprocs_1334_);
v_dischargeWrapper_1335_ = lean_ctor_get(v_a_1326_, 2);
lean_inc(v_dischargeWrapper_1335_);
lean_dec(v_a_1326_);
v___x_1336_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1333_);
v___y_1239_ = v_dischargeWrapper_1335_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v_simprocs_1334_;
v___y_1242_ = v___y_1322_;
v___y_1243_ = v___y_1319_;
v___y_1244_ = v___y_1321_;
v___y_1245_ = v___y_1316_;
v___y_1246_ = v___y_1315_;
v___y_1247_ = v___y_1318_;
v___y_1248_ = v___y_1320_;
v___y_1249_ = v_stxForSuggestion_1314_;
v___y_1250_ = v___y_1317_;
v___y_1251_ = v___x_1336_;
goto v___jp_1238_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_stxForSuggestion_1314_);
lean_dec(v___y_1312_);
lean_dec(v___y_1309_);
lean_dec(v_tk_1237_);
v_a_1337_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1325_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1325_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v___y_1350_);
v___x_1369_ = l_Array_append___redArg(v___y_1350_, v___y_1368_);
lean_dec_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc(v___y_1353_);
v___x_1370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1370_, 0, v___y_1353_);
lean_ctor_set(v___x_1370_, 1, v___y_1367_);
lean_ctor_set(v___x_1370_, 2, v___x_1369_);
v___x_1371_ = l_Lean_Syntax_node6(v___y_1353_, v___y_1366_, v___y_1354_, v___y_1360_, v___y_1363_, v___y_1362_, v___y_1351_, v___x_1370_);
v___y_1309_ = v___y_1346_;
v___y_1310_ = v___y_1359_;
v___y_1311_ = v___y_1358_;
v___y_1312_ = v___y_1347_;
v___y_1313_ = v___y_1356_;
v_stxForSuggestion_1314_ = v___x_1371_;
v___y_1315_ = v___y_1361_;
v___y_1316_ = v___y_1355_;
v___y_1317_ = v___y_1364_;
v___y_1318_ = v___y_1352_;
v___y_1319_ = v___y_1349_;
v___y_1320_ = v___y_1365_;
v___y_1321_ = v___y_1348_;
v___y_1322_ = v___y_1357_;
goto v___jp_1308_;
}
v___jp_1372_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_inc_ref_n(v___y_1375_, 2);
v___x_1396_ = l_Array_append___redArg(v___y_1375_, v___y_1395_);
lean_dec_ref(v___y_1395_);
lean_inc_n(v___y_1394_, 3);
lean_inc_n(v___y_1380_, 5);
v___x_1397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1380_);
lean_ctor_set(v___x_1397_, 1, v___y_1394_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1380_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1401_ = l_Lean_Syntax_SepArray_ofElems(v___x_1400_, v___y_1374_);
lean_dec_ref(v___y_1374_);
v___x_1402_ = l_Array_append___redArg(v___y_1375_, v___x_1401_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1380_);
lean_ctor_set(v___x_1403_, 1, v___y_1394_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1380_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = l_Lean_Syntax_node3(v___y_1380_, v___y_1394_, v___x_1399_, v___x_1403_, v___x_1405_);
if (lean_obj_tag(v___y_1392_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1408_; 
v_val_1407_ = lean_ctor_get(v___y_1392_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v___y_1392_, 1);
v___x_1408_ = l_Array_mkArray1___redArg(v_val_1407_);
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1376_;
v___y_1348_ = v___y_1377_;
v___y_1349_ = v___y_1378_;
v___y_1350_ = v___y_1375_;
v___y_1351_ = v___x_1406_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1386_;
v___y_1359_ = v___y_1385_;
v___y_1360_ = v___y_1388_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___x_1397_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1390_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1394_;
v___y_1368_ = v___x_1408_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1409_; 
lean_dec(v___y_1392_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1376_;
v___y_1348_ = v___y_1377_;
v___y_1349_ = v___y_1378_;
v___y_1350_ = v___y_1375_;
v___y_1351_ = v___x_1406_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1386_;
v___y_1359_ = v___y_1385_;
v___y_1360_ = v___y_1388_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___x_1397_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1390_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1394_;
v___y_1368_ = v___x_1409_;
goto v___jp_1345_;
}
}
v___jp_1410_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_inc_ref(v___y_1413_);
v___x_1434_ = l_Array_append___redArg(v___y_1413_, v___y_1433_);
lean_dec_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc(v___y_1418_);
v___x_1435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1418_);
lean_ctor_set(v___x_1435_, 1, v___y_1432_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
if (lean_obj_tag(v___y_1420_) == 1)
{
lean_object* v_val_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_val_1436_ = lean_ctor_get(v___y_1420_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___y_1420_, 1);
v___x_1437_ = l_Lean_SourceInfo_fromRef(v_val_1436_, v___x_1221_);
lean_dec(v_val_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Array_mkArray1___redArg(v___x_1439_);
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1422_;
v___y_1384_ = v___y_1423_;
v___y_1385_ = v___y_1425_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1427_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1435_;
v___y_1390_ = v___y_1428_;
v___y_1391_ = v___y_1429_;
v___y_1392_ = v___y_1431_;
v___y_1393_ = v___y_1430_;
v___y_1394_ = v___y_1432_;
v___y_1395_ = v___x_1440_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1441_; 
lean_dec(v___y_1420_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1422_;
v___y_1384_ = v___y_1423_;
v___y_1385_ = v___y_1425_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1427_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1435_;
v___y_1390_ = v___y_1428_;
v___y_1391_ = v___y_1429_;
v___y_1392_ = v___y_1431_;
v___y_1393_ = v___y_1430_;
v___y_1394_ = v___y_1432_;
v___y_1395_ = v___x_1441_;
goto v___jp_1372_;
}
}
v___jp_1442_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v___y_1447_);
v___x_1466_ = l_Array_append___redArg(v___y_1447_, v___y_1465_);
lean_dec_ref(v___y_1465_);
lean_inc(v___y_1449_);
lean_inc(v___y_1462_);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1462_);
lean_ctor_set(v___x_1467_, 1, v___y_1449_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node6(v___y_1462_, v___y_1452_, v___y_1448_, v___y_1459_, v___y_1453_, v___y_1461_, v___y_1450_, v___x_1467_);
v___y_1309_ = v___y_1443_;
v___y_1310_ = v___y_1458_;
v___y_1311_ = v___y_1457_;
v___y_1312_ = v___y_1444_;
v___y_1313_ = v___y_1455_;
v_stxForSuggestion_1314_ = v___x_1468_;
v___y_1315_ = v___y_1460_;
v___y_1316_ = v___y_1454_;
v___y_1317_ = v___y_1463_;
v___y_1318_ = v___y_1451_;
v___y_1319_ = v___y_1446_;
v___y_1320_ = v___y_1464_;
v___y_1321_ = v___y_1445_;
v___y_1322_ = v___y_1456_;
goto v___jp_1308_;
}
v___jp_1469_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc_ref_n(v___y_1475_, 2);
v___x_1493_ = l_Array_append___redArg(v___y_1475_, v___y_1492_);
lean_dec_ref(v___y_1492_);
lean_inc_n(v___y_1477_, 3);
lean_inc_n(v___y_1488_, 5);
v___x_1494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1488_);
lean_ctor_set(v___x_1494_, 1, v___y_1477_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1488_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1498_ = l_Lean_Syntax_SepArray_ofElems(v___x_1497_, v___y_1471_);
lean_dec_ref(v___y_1471_);
v___x_1499_ = l_Array_append___redArg(v___y_1475_, v___x_1498_);
lean_dec_ref(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1488_);
lean_ctor_set(v___x_1500_, 1, v___y_1477_);
lean_ctor_set(v___x_1500_, 2, v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1488_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_Syntax_node3(v___y_1488_, v___y_1477_, v___x_1496_, v___x_1500_, v___x_1502_);
if (lean_obj_tag(v___y_1491_) == 1)
{
lean_object* v_val_1504_; lean_object* v___x_1505_; 
v_val_1504_ = lean_ctor_get(v___y_1491_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___y_1491_, 1);
v___x_1505_ = l_Array_mkArray1___redArg(v_val_1504_);
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1472_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1477_;
v___y_1450_ = v___x_1503_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1479_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1485_;
v___y_1458_ = v___y_1484_;
v___y_1459_ = v___y_1487_;
v___y_1460_ = v___y_1486_;
v___y_1461_ = v___x_1494_;
v___y_1462_ = v___y_1488_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___x_1505_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v___y_1491_);
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1472_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1477_;
v___y_1450_ = v___x_1503_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1479_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1485_;
v___y_1458_ = v___y_1484_;
v___y_1459_ = v___y_1487_;
v___y_1460_ = v___y_1486_;
v___y_1461_ = v___x_1494_;
v___y_1462_ = v___y_1488_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___x_1506_;
goto v___jp_1442_;
}
}
v___jp_1507_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_inc_ref(v___y_1513_);
v___x_1531_ = l_Array_append___redArg(v___y_1513_, v___y_1530_);
lean_dec_ref(v___y_1530_);
lean_inc(v___y_1515_);
lean_inc(v___y_1526_);
v___x_1532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1526_);
lean_ctor_set(v___x_1532_, 1, v___y_1515_);
lean_ctor_set(v___x_1532_, 2, v___x_1531_);
if (lean_obj_tag(v___y_1518_) == 1)
{
lean_object* v_val_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_val_1533_ = lean_ctor_get(v___y_1518_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___y_1518_, 1);
v___x_1534_ = l_Lean_SourceInfo_fromRef(v_val_1533_, v___x_1221_);
lean_dec(v_val_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Array_mkArray1___redArg(v___x_1536_);
v___y_1470_ = v___y_1508_;
v___y_1471_ = v___y_1509_;
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___x_1532_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___y_1522_;
v___y_1486_ = v___y_1525_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___y_1526_;
v___y_1489_ = v___y_1527_;
v___y_1490_ = v___y_1528_;
v___y_1491_ = v___y_1529_;
v___y_1492_ = v___x_1537_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1538_; 
lean_dec(v___y_1518_);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1470_ = v___y_1508_;
v___y_1471_ = v___y_1509_;
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___x_1532_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___y_1522_;
v___y_1486_ = v___y_1525_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___y_1526_;
v___y_1489_ = v___y_1527_;
v___y_1490_ = v___y_1528_;
v___y_1491_ = v___y_1529_;
v___y_1492_ = v___x_1538_;
goto v___jp_1469_;
}
}
v___jp_1539_:
{
lean_object* v_ref_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_ref_1559_ = lean_ctor_get(v___y_1542_, 5);
v___x_1560_ = l_Lean_SourceInfo_fromRef(v_ref_1559_, v___y_1558_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1562_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_1561_);
v___x_1563_ = l_Lean_SourceInfo_fromRef(v_tk_1237_, v___x_1221_);
v___x_1564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1561_);
v___x_1565_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1566_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1554_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1568_; 
v_val_1567_ = lean_ctor_get(v___y_1554_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___y_1554_, 1);
v___x_1568_ = l_Array_mkArray1___redArg(v_val_1567_);
v___y_1508_ = v___y_1540_;
v___y_1509_ = v___y_1541_;
v___y_1510_ = v___y_1543_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1544_;
v___y_1513_ = v___x_1566_;
v___y_1514_ = v___x_1564_;
v___y_1515_ = v___x_1565_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___x_1562_;
v___y_1518_ = v___y_1546_;
v___y_1519_ = v___y_1547_;
v___y_1520_ = v___y_1548_;
v___y_1521_ = v___y_1549_;
v___y_1522_ = v___y_1550_;
v___y_1523_ = v___y_1551_;
v___y_1524_ = v___y_1553_;
v___y_1525_ = v___y_1552_;
v___y_1526_ = v___x_1560_;
v___y_1527_ = v___y_1555_;
v___y_1528_ = v___y_1556_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___x_1568_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1569_; 
lean_dec(v___y_1554_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1508_ = v___y_1540_;
v___y_1509_ = v___y_1541_;
v___y_1510_ = v___y_1543_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1544_;
v___y_1513_ = v___x_1566_;
v___y_1514_ = v___x_1564_;
v___y_1515_ = v___x_1565_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___x_1562_;
v___y_1518_ = v___y_1546_;
v___y_1519_ = v___y_1547_;
v___y_1520_ = v___y_1548_;
v___y_1521_ = v___y_1549_;
v___y_1522_ = v___y_1550_;
v___y_1523_ = v___y_1551_;
v___y_1524_ = v___y_1553_;
v___y_1525_ = v___y_1552_;
v___y_1526_ = v___x_1560_;
v___y_1527_ = v___y_1555_;
v___y_1528_ = v___y_1556_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___x_1569_;
goto v___jp_1507_;
}
}
v___jp_1570_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___y_1575_) == 0)
{
lean_object* v_a_1590_; uint8_t v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = 0;
v___y_1540_ = v___y_1571_;
v___y_1541_ = v___y_1573_;
v___y_1542_ = v___y_1587_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1585_;
v___y_1545_ = v___y_1584_;
v___y_1546_ = v___y_1577_;
v___y_1547_ = v___y_1582_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1588_;
v___y_1550_ = v_stxForExecution_1580_;
v___y_1551_ = v___y_1574_;
v___y_1552_ = v___y_1581_;
v___y_1553_ = v_a_1590_;
v___y_1554_ = v___y_1576_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1586_;
v___y_1557_ = v___y_1578_;
v___y_1558_ = v___x_1591_;
goto v___jp_1539_;
}
else
{
if (v___y_1579_ == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1589_);
v___y_1540_ = v___y_1571_;
v___y_1541_ = v___y_1573_;
v___y_1542_ = v___y_1587_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1585_;
v___y_1545_ = v___y_1584_;
v___y_1546_ = v___y_1577_;
v___y_1547_ = v___y_1582_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1588_;
v___y_1550_ = v_stxForExecution_1580_;
v___y_1551_ = v___y_1574_;
v___y_1552_ = v___y_1581_;
v___y_1553_ = v_a_1592_;
v___y_1554_ = v___y_1576_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1586_;
v___y_1557_ = v___y_1578_;
v___y_1558_ = v___y_1579_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1593_; lean_object* v_ref_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1593_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1589_);
v_ref_1594_ = lean_ctor_get(v___y_1587_, 5);
v___x_1595_ = 0;
v___x_1596_ = l_Lean_SourceInfo_fromRef(v_ref_1594_, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1598_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_1597_);
v___x_1599_ = l_Lean_SourceInfo_fromRef(v_tk_1237_, v___x_1221_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1603_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1576_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1605_; 
v_val_1604_ = lean_ctor_get(v___y_1576_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v___y_1576_, 1);
v___x_1605_ = l_Array_mkArray1___redArg(v_val_1604_);
v___y_1411_ = v___y_1571_;
v___y_1412_ = v___y_1573_;
v___y_1413_ = v___x_1603_;
v___y_1414_ = v___y_1575_;
v___y_1415_ = v___y_1587_;
v___y_1416_ = v___y_1585_;
v___y_1417_ = v___y_1584_;
v___y_1418_ = v___x_1596_;
v___y_1419_ = v___x_1601_;
v___y_1420_ = v___y_1577_;
v___y_1421_ = v___y_1582_;
v___y_1422_ = v___y_1579_;
v___y_1423_ = v___y_1588_;
v___y_1424_ = v_stxForExecution_1580_;
v___y_1425_ = v___y_1574_;
v___y_1426_ = v_a_1593_;
v___y_1427_ = v___y_1581_;
v___y_1428_ = v___y_1583_;
v___y_1429_ = v___y_1586_;
v___y_1430_ = v___x_1598_;
v___y_1431_ = v___y_1578_;
v___y_1432_ = v___x_1602_;
v___y_1433_ = v___x_1605_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1606_; 
lean_dec(v___y_1576_);
v___x_1606_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1411_ = v___y_1571_;
v___y_1412_ = v___y_1573_;
v___y_1413_ = v___x_1603_;
v___y_1414_ = v___y_1575_;
v___y_1415_ = v___y_1587_;
v___y_1416_ = v___y_1585_;
v___y_1417_ = v___y_1584_;
v___y_1418_ = v___x_1596_;
v___y_1419_ = v___x_1601_;
v___y_1420_ = v___y_1577_;
v___y_1421_ = v___y_1582_;
v___y_1422_ = v___y_1579_;
v___y_1423_ = v___y_1588_;
v___y_1424_ = v_stxForExecution_1580_;
v___y_1425_ = v___y_1574_;
v___y_1426_ = v_a_1593_;
v___y_1427_ = v___y_1581_;
v___y_1428_ = v___y_1583_;
v___y_1429_ = v___y_1586_;
v___y_1430_ = v___x_1598_;
v___y_1431_ = v___y_1578_;
v___y_1432_ = v___x_1602_;
v___y_1433_ = v___x_1606_;
goto v___jp_1410_;
}
}
}
}
v___jp_1607_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v___y_1619_);
v___x_1634_ = l_Array_append___redArg(v___y_1619_, v___y_1633_);
lean_dec_ref(v___y_1633_);
lean_inc(v___y_1627_);
lean_inc(v___y_1632_);
v___x_1635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1632_);
lean_ctor_set(v___x_1635_, 1, v___y_1627_);
lean_ctor_set(v___x_1635_, 2, v___x_1634_);
lean_inc(v___y_1622_);
v___x_1636_ = l_Lean_Syntax_node6(v___y_1632_, v___y_1611_, v___y_1615_, v___y_1622_, v___y_1625_, v___y_1614_, v___y_1618_, v___x_1635_);
v___y_1571_ = v___y_1608_;
v___y_1572_ = v___y_1622_;
v___y_1573_ = v___y_1609_;
v___y_1574_ = v___y_1616_;
v___y_1575_ = v___y_1610_;
v___y_1576_ = v___y_1630_;
v___y_1577_ = v___y_1624_;
v___y_1578_ = v___y_1631_;
v___y_1579_ = v___y_1613_;
v_stxForExecution_1580_ = v___x_1636_;
v___y_1581_ = v___y_1629_;
v___y_1582_ = v___y_1623_;
v___y_1583_ = v___y_1626_;
v___y_1584_ = v___y_1620_;
v___y_1585_ = v___y_1617_;
v___y_1586_ = v___y_1628_;
v___y_1587_ = v___y_1621_;
v___y_1588_ = v___y_1612_;
goto v___jp_1570_;
}
v___jp_1637_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref_n(v___y_1656_, 2);
v___x_1662_ = l_Array_append___redArg(v___y_1656_, v___y_1661_);
lean_dec_ref(v___y_1661_);
lean_inc_n(v___y_1650_, 3);
lean_inc_n(v___y_1660_, 5);
v___x_1663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1660_);
lean_ctor_set(v___x_1663_, 1, v___y_1650_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
v___x_1664_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1660_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1667_ = l_Lean_Syntax_SepArray_ofElems(v___x_1666_, v___y_1640_);
v___x_1668_ = l_Array_append___redArg(v___y_1656_, v___x_1667_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1660_);
lean_ctor_set(v___x_1669_, 1, v___y_1650_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
v___x_1670_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1660_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_Syntax_node3(v___y_1660_, v___y_1650_, v___x_1665_, v___x_1669_, v___x_1671_);
if (lean_obj_tag(v___y_1658_) == 1)
{
lean_object* v_val_1673_; lean_object* v___x_1674_; 
v_val_1673_ = lean_ctor_get(v___y_1658_, 0);
lean_inc(v_val_1673_);
v___x_1674_ = l_Array_mkArray1___redArg(v_val_1673_);
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1640_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___y_1646_;
v___y_1613_ = v___y_1647_;
v___y_1614_ = v___x_1663_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___y_1651_;
v___y_1617_ = v___y_1653_;
v___y_1618_ = v___x_1672_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___y_1659_;
v___y_1622_ = v___y_1639_;
v___y_1623_ = v___y_1641_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1650_;
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___x_1674_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1640_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___y_1646_;
v___y_1613_ = v___y_1647_;
v___y_1614_ = v___x_1663_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___y_1651_;
v___y_1617_ = v___y_1653_;
v___y_1618_ = v___x_1672_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___y_1659_;
v___y_1622_ = v___y_1639_;
v___y_1623_ = v___y_1641_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1650_;
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___x_1675_;
goto v___jp_1607_;
}
}
v___jp_1676_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_inc_ref(v___y_1694_);
v___x_1700_ = l_Array_append___redArg(v___y_1694_, v___y_1699_);
lean_dec_ref(v___y_1699_);
lean_inc(v___y_1689_);
lean_inc(v___y_1698_);
v___x_1701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___y_1698_);
lean_ctor_set(v___x_1701_, 1, v___y_1689_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
if (lean_obj_tag(v___y_1683_) == 1)
{
lean_object* v_val_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_val_1702_ = lean_ctor_get(v___y_1683_, 0);
v___x_1703_ = l_Lean_SourceInfo_fromRef(v_val_1702_, v___x_1221_);
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Array_mkArray1___redArg(v___x_1705_);
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1683_;
v___y_1645_ = v___x_1701_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1688_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___y_1690_;
v___y_1654_ = v___y_1693_;
v___y_1655_ = v___y_1692_;
v___y_1656_ = v___y_1694_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___x_1706_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1683_;
v___y_1645_ = v___x_1701_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1688_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___y_1690_;
v___y_1654_ = v___y_1693_;
v___y_1655_ = v___y_1692_;
v___y_1656_ = v___y_1694_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___x_1707_;
goto v___jp_1637_;
}
}
v___jp_1708_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc_ref(v___y_1723_);
v___x_1735_ = l_Array_append___redArg(v___y_1723_, v___y_1734_);
lean_dec_ref(v___y_1734_);
lean_inc(v___y_1722_);
lean_inc(v___y_1716_);
v___x_1736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1716_);
lean_ctor_set(v___x_1736_, 1, v___y_1722_);
lean_ctor_set(v___x_1736_, 2, v___x_1735_);
lean_inc(v___y_1725_);
v___x_1737_ = l_Lean_Syntax_node6(v___y_1716_, v___y_1727_, v___y_1710_, v___y_1725_, v___y_1718_, v___y_1715_, v___y_1721_, v___x_1736_);
v___y_1571_ = v___y_1709_;
v___y_1572_ = v___y_1725_;
v___y_1573_ = v___y_1711_;
v___y_1574_ = v___y_1717_;
v___y_1575_ = v___y_1712_;
v___y_1576_ = v___y_1732_;
v___y_1577_ = v___y_1728_;
v___y_1578_ = v___y_1733_;
v___y_1579_ = v___y_1714_;
v_stxForExecution_1580_ = v___x_1737_;
v___y_1581_ = v___y_1731_;
v___y_1582_ = v___y_1726_;
v___y_1583_ = v___y_1729_;
v___y_1584_ = v___y_1720_;
v___y_1585_ = v___y_1719_;
v___y_1586_ = v___y_1730_;
v___y_1587_ = v___y_1724_;
v___y_1588_ = v___y_1713_;
goto v___jp_1570_;
}
v___jp_1738_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_inc_ref_n(v___y_1760_, 2);
v___x_1763_ = l_Array_append___redArg(v___y_1760_, v___y_1762_);
lean_dec_ref(v___y_1762_);
lean_inc_n(v___y_1761_, 3);
lean_inc_n(v___y_1750_, 5);
v___x_1764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1764_, 0, v___y_1750_);
lean_ctor_set(v___x_1764_, 1, v___y_1761_);
lean_ctor_set(v___x_1764_, 2, v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1750_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1768_ = l_Lean_Syntax_SepArray_ofElems(v___x_1767_, v___y_1741_);
v___x_1769_ = l_Array_append___redArg(v___y_1760_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1750_);
lean_ctor_set(v___x_1770_, 1, v___y_1761_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___y_1750_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_node3(v___y_1750_, v___y_1761_, v___x_1766_, v___x_1770_, v___x_1772_);
if (lean_obj_tag(v___y_1758_) == 1)
{
lean_object* v_val_1774_; lean_object* v___x_1775_; 
v_val_1774_ = lean_ctor_get(v___y_1758_, 0);
lean_inc(v_val_1774_);
v___x_1775_ = l_Array_mkArray1___redArg(v_val_1774_);
v___y_1709_ = v___y_1739_;
v___y_1710_ = v___y_1742_;
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1744_;
v___y_1713_ = v___y_1747_;
v___y_1714_ = v___y_1748_;
v___y_1715_ = v___x_1764_;
v___y_1716_ = v___y_1750_;
v___y_1717_ = v___y_1751_;
v___y_1718_ = v___y_1753_;
v___y_1719_ = v___y_1754_;
v___y_1720_ = v___y_1757_;
v___y_1721_ = v___x_1773_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___y_1759_;
v___y_1725_ = v___y_1740_;
v___y_1726_ = v___y_1743_;
v___y_1727_ = v___y_1745_;
v___y_1728_ = v___y_1746_;
v___y_1729_ = v___y_1749_;
v___y_1730_ = v___y_1752_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___x_1775_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1709_ = v___y_1739_;
v___y_1710_ = v___y_1742_;
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1744_;
v___y_1713_ = v___y_1747_;
v___y_1714_ = v___y_1748_;
v___y_1715_ = v___x_1764_;
v___y_1716_ = v___y_1750_;
v___y_1717_ = v___y_1751_;
v___y_1718_ = v___y_1753_;
v___y_1719_ = v___y_1754_;
v___y_1720_ = v___y_1757_;
v___y_1721_ = v___x_1773_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___y_1759_;
v___y_1725_ = v___y_1740_;
v___y_1726_ = v___y_1743_;
v___y_1727_ = v___y_1745_;
v___y_1728_ = v___y_1746_;
v___y_1729_ = v___y_1749_;
v___y_1730_ = v___y_1752_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___x_1776_;
goto v___jp_1708_;
}
}
v___jp_1777_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_inc_ref(v___y_1798_);
v___x_1801_ = l_Array_append___redArg(v___y_1798_, v___y_1800_);
lean_dec_ref(v___y_1800_);
lean_inc(v___y_1799_);
lean_inc(v___y_1789_);
v___x_1802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1789_);
lean_ctor_set(v___x_1802_, 1, v___y_1799_);
lean_ctor_set(v___x_1802_, 2, v___x_1801_);
if (lean_obj_tag(v___y_1785_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_val_1803_ = lean_ctor_get(v___y_1785_, 0);
v___x_1804_ = l_Lean_SourceInfo_fromRef(v_val_1803_, v___x_1221_);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Array_mkArray1___redArg(v___x_1806_);
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1792_;
v___y_1753_ = v___x_1802_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___y_1794_;
v___y_1756_ = v___y_1793_;
v___y_1757_ = v___y_1795_;
v___y_1758_ = v___y_1796_;
v___y_1759_ = v___y_1797_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___y_1799_;
v___y_1762_ = v___x_1807_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1792_;
v___y_1753_ = v___x_1802_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___y_1794_;
v___y_1756_ = v___y_1793_;
v___y_1757_ = v___y_1795_;
v___y_1758_ = v___y_1796_;
v___y_1759_ = v___y_1797_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___y_1799_;
v___y_1762_ = v___x_1808_;
goto v___jp_1738_;
}
}
v___jp_1809_:
{
lean_object* v_ref_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_ref_1828_ = lean_ctor_get(v___y_1826_, 5);
v___x_1829_ = l_Lean_SourceInfo_fromRef(v_ref_1828_, v___y_1827_);
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc_ref(v___x_1222_);
v___x_1831_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_1830_);
v___x_1832_ = l_Lean_SourceInfo_fromRef(v_tk_1237_, v___x_1221_);
v___x_1833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1830_);
v___x_1834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1835_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1822_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1837_; 
v_val_1836_ = lean_ctor_get(v___y_1822_, 0);
lean_inc(v_val_1836_);
v___x_1837_ = l_Array_mkArray1___redArg(v_val_1836_);
v___y_1778_ = v___y_1810_;
v___y_1779_ = v___y_1811_;
v___y_1780_ = v___y_1812_;
v___y_1781_ = v___x_1833_;
v___y_1782_ = v___y_1813_;
v___y_1783_ = v___y_1814_;
v___y_1784_ = v___x_1831_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___y_1818_;
v___y_1789_ = v___x_1829_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1823_;
v___y_1794_ = v___y_1822_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___y_1825_;
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___x_1835_;
v___y_1799_ = v___x_1834_;
v___y_1800_ = v___x_1837_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1778_ = v___y_1810_;
v___y_1779_ = v___y_1811_;
v___y_1780_ = v___y_1812_;
v___y_1781_ = v___x_1833_;
v___y_1782_ = v___y_1813_;
v___y_1783_ = v___y_1814_;
v___y_1784_ = v___x_1831_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___y_1818_;
v___y_1789_ = v___x_1829_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1823_;
v___y_1794_ = v___y_1822_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___y_1825_;
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___x_1835_;
v___y_1799_ = v___x_1834_;
v___y_1800_ = v___x_1838_;
goto v___jp_1777_;
}
}
v___jp_1839_:
{
if (lean_obj_tag(v___y_1843_) == 0)
{
uint8_t v___x_1857_; 
v___x_1857_ = 0;
v___y_1810_ = v___y_1840_;
v___y_1811_ = v___y_1841_;
v___y_1812_ = v_argsArray_1848_;
v___y_1813_ = v___y_1850_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___y_1846_;
v___y_1818_ = v___y_1851_;
v___y_1819_ = v___y_1842_;
v___y_1820_ = v___y_1853_;
v___y_1821_ = v___y_1854_;
v___y_1822_ = v___y_1844_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1852_;
v___y_1825_ = v___y_1847_;
v___y_1826_ = v___y_1855_;
v___y_1827_ = v___x_1857_;
goto v___jp_1809_;
}
else
{
if (v___y_1846_ == 0)
{
v___y_1810_ = v___y_1840_;
v___y_1811_ = v___y_1841_;
v___y_1812_ = v_argsArray_1848_;
v___y_1813_ = v___y_1850_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___y_1846_;
v___y_1818_ = v___y_1851_;
v___y_1819_ = v___y_1842_;
v___y_1820_ = v___y_1853_;
v___y_1821_ = v___y_1854_;
v___y_1822_ = v___y_1844_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1852_;
v___y_1825_ = v___y_1847_;
v___y_1826_ = v___y_1855_;
v___y_1827_ = v___y_1846_;
goto v___jp_1809_;
}
else
{
lean_object* v_ref_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_ref_1858_ = lean_ctor_get(v___y_1855_, 5);
v___x_1859_ = 0;
v___x_1860_ = l_Lean_SourceInfo_fromRef(v_ref_1858_, v___x_1859_);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc_ref(v___x_1222_);
v___x_1862_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_1861_);
v___x_1863_ = l_Lean_SourceInfo_fromRef(v_tk_1237_, v___x_1221_);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1867_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1844_) == 1)
{
lean_object* v_val_1868_; lean_object* v___x_1869_; 
v_val_1868_ = lean_ctor_get(v___y_1844_, 0);
lean_inc(v_val_1868_);
v___x_1869_ = l_Array_mkArray1___redArg(v_val_1868_);
v___y_1677_ = v___y_1840_;
v___y_1678_ = v___y_1841_;
v___y_1679_ = v_argsArray_1848_;
v___y_1680_ = v___y_1850_;
v___y_1681_ = v___y_1843_;
v___y_1682_ = v___x_1862_;
v___y_1683_ = v___y_1845_;
v___y_1684_ = v___y_1856_;
v___y_1685_ = v___y_1846_;
v___y_1686_ = v___y_1851_;
v___y_1687_ = v___x_1865_;
v___y_1688_ = v___y_1842_;
v___y_1689_ = v___x_1866_;
v___y_1690_ = v___y_1853_;
v___y_1691_ = v___y_1854_;
v___y_1692_ = v___y_1849_;
v___y_1693_ = v___y_1844_;
v___y_1694_ = v___x_1867_;
v___y_1695_ = v___y_1852_;
v___y_1696_ = v___y_1847_;
v___y_1697_ = v___y_1855_;
v___y_1698_ = v___x_1860_;
v___y_1699_ = v___x_1869_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1677_ = v___y_1840_;
v___y_1678_ = v___y_1841_;
v___y_1679_ = v_argsArray_1848_;
v___y_1680_ = v___y_1850_;
v___y_1681_ = v___y_1843_;
v___y_1682_ = v___x_1862_;
v___y_1683_ = v___y_1845_;
v___y_1684_ = v___y_1856_;
v___y_1685_ = v___y_1846_;
v___y_1686_ = v___y_1851_;
v___y_1687_ = v___x_1865_;
v___y_1688_ = v___y_1842_;
v___y_1689_ = v___x_1866_;
v___y_1690_ = v___y_1853_;
v___y_1691_ = v___y_1854_;
v___y_1692_ = v___y_1849_;
v___y_1693_ = v___y_1844_;
v___y_1694_ = v___x_1867_;
v___y_1695_ = v___y_1852_;
v___y_1696_ = v___y_1847_;
v___y_1697_ = v___y_1855_;
v___y_1698_ = v___x_1860_;
v___y_1699_ = v___x_1870_;
goto v___jp_1676_;
}
}
}
}
v___jp_1871_:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1875_, v___y_1881_, v___y_1885_, v___y_1888_, v___y_1874_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l_Lean_LibrarySuggestions_select(v_a_1891_, v___y_1889_, v___y_1881_, v___y_1885_, v___y_1888_, v___y_1874_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; size_t v_sz_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v_sz_1894_ = lean_array_size(v_a_1893_);
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1893_, v_sz_1894_, v___x_1895_, v___y_1882_, v___y_1877_, v___y_1875_, v___y_1879_, v___y_1886_, v___y_1881_, v___y_1885_, v___y_1888_, v___y_1874_);
lean_dec(v_a_1893_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___y_1840_ = v___y_1872_;
v___y_1841_ = v___y_1873_;
v___y_1842_ = v___y_1883_;
v___y_1843_ = v___y_1876_;
v___y_1844_ = v___y_1884_;
v___y_1845_ = v___y_1878_;
v___y_1846_ = v___y_1880_;
v___y_1847_ = v___y_1887_;
v_argsArray_1848_ = v_a_1897_;
v___y_1849_ = v___y_1877_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1879_;
v___y_1852_ = v___y_1886_;
v___y_1853_ = v___y_1881_;
v___y_1854_ = v___y_1885_;
v___y_1855_ = v___y_1888_;
v___y_1856_ = v___y_1874_;
goto v___jp_1839_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___y_1887_);
lean_dec(v___y_1884_);
lean_dec(v___y_1878_);
lean_dec(v___y_1876_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_a_1898_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1896_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v___y_1887_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1878_);
lean_dec(v___y_1876_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_a_1906_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1892_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1892_);
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
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1887_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1878_);
lean_dec(v___y_1876_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_a_1914_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1890_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1890_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
v___jp_1922_:
{
lean_object* v_config_1941_; uint8_t v_suggestions_1942_; 
v_config_1941_ = lean_ctor_get(v___y_1934_, 0);
lean_inc_ref(v_config_1941_);
lean_dec_ref(v___y_1934_);
v_suggestions_1942_ = lean_ctor_get_uint8(v_config_1941_, sizeof(void*)*3 + 26);
if (v_suggestions_1942_ == 0)
{
lean_dec_ref(v_config_1941_);
lean_dec_ref(v___f_1225_);
v___y_1840_ = v___y_1923_;
v___y_1841_ = v___y_1924_;
v___y_1842_ = v___y_1933_;
v___y_1843_ = v___y_1927_;
v___y_1844_ = v___y_1935_;
v___y_1845_ = v___y_1929_;
v___y_1846_ = v___y_1931_;
v___y_1847_ = v___y_1938_;
v_argsArray_1848_ = v___y_1940_;
v___y_1849_ = v___y_1928_;
v___y_1850_ = v___y_1926_;
v___y_1851_ = v___y_1930_;
v___y_1852_ = v___y_1937_;
v___y_1853_ = v___y_1932_;
v___y_1854_ = v___y_1936_;
v___y_1855_ = v___y_1939_;
v___y_1856_ = v___y_1925_;
goto v___jp_1839_;
}
else
{
lean_object* v_maxSuggestions_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_maxSuggestions_1943_ = lean_ctor_get(v_config_1941_, 2);
lean_inc(v_maxSuggestions_1943_);
lean_dec_ref(v_config_1941_);
v___x_1944_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1945_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1943_) == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_unsigned_to_nat(100u);
v___x_1947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1944_);
lean_ctor_set(v___x_1947_, 2, v___f_1225_);
lean_ctor_set(v___x_1947_, 3, v___x_1945_);
v___y_1872_ = v___y_1923_;
v___y_1873_ = v___y_1924_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___y_1940_;
v___y_1883_ = v___y_1933_;
v___y_1884_ = v___y_1935_;
v___y_1885_ = v___y_1936_;
v___y_1886_ = v___y_1937_;
v___y_1887_ = v___y_1938_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___x_1947_;
goto v___jp_1871_;
}
else
{
lean_object* v_val_1948_; lean_object* v___x_1949_; 
v_val_1948_ = lean_ctor_get(v_maxSuggestions_1943_, 0);
lean_inc(v_val_1948_);
lean_dec_ref_known(v_maxSuggestions_1943_, 1);
v___x_1949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1949_, 0, v_val_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1944_);
lean_ctor_set(v___x_1949_, 2, v___f_1225_);
lean_ctor_set(v___x_1949_, 3, v___x_1945_);
v___y_1872_ = v___y_1923_;
v___y_1873_ = v___y_1924_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___y_1940_;
v___y_1883_ = v___y_1933_;
v___y_1884_ = v___y_1935_;
v___y_1885_ = v___y_1936_;
v___y_1886_ = v___y_1937_;
v___y_1887_ = v___y_1938_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___x_1949_;
goto v___jp_1871_;
}
}
}
v___jp_1950_:
{
uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = 0;
lean_inc(v___y_1957_);
v___x_1967_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1957_, v___x_1966_, v___y_1955_, v___y_1954_, v___y_1963_);
if (lean_obj_tag(v___x_1967_) == 0)
{
if (lean_obj_tag(v___y_1962_) == 1)
{
lean_object* v_a_1968_; lean_object* v_val_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v_val_1969_ = lean_ctor_get(v___y_1962_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___y_1962_, 1);
v___x_1970_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1969_);
lean_dec(v_val_1969_);
lean_inc(v___y_1958_);
v___y_1923_ = v___y_1958_;
v___y_1924_ = v___y_1957_;
v___y_1925_ = v___y_1963_;
v___y_1926_ = v___y_1951_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1955_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1964_;
v___y_1931_ = v___y_1956_;
v___y_1932_ = v___y_1959_;
v___y_1933_ = v___x_1966_;
v___y_1934_ = v_a_1968_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1952_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___y_1954_;
v___y_1940_ = v___x_1970_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
lean_dec(v___y_1962_);
v_a_1971_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1958_);
v___y_1923_ = v___y_1958_;
v___y_1924_ = v___y_1957_;
v___y_1925_ = v___y_1963_;
v___y_1926_ = v___y_1951_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1955_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1964_;
v___y_1931_ = v___y_1956_;
v___y_1932_ = v___y_1959_;
v___y_1933_ = v___x_1966_;
v___y_1934_ = v_a_1971_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1952_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___y_1954_;
v___y_1940_ = v___x_1972_;
goto v___jp_1922_;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v___y_1965_);
lean_dec(v___y_1962_);
lean_dec(v___y_1960_);
lean_dec(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1953_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_a_1973_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1967_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1967_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
v___jp_1981_:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Syntax_getOptional_x3f(v___y_1992_);
lean_dec(v___y_1992_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_box(0);
v___y_1951_ = v___y_1985_;
v___y_1952_ = v___y_1993_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1995_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___y_1990_;
v___y_1957_ = v___y_1982_;
v___y_1958_ = v___y_1996_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1994_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1983_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___x_1998_;
goto v___jp_1950_;
}
else
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_val_1999_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1997_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v___x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_val_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v___y_1951_ = v___y_1985_;
v___y_1952_ = v___y_1993_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1995_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___y_1990_;
v___y_1957_ = v___y_1982_;
v___y_1958_ = v___y_1996_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1994_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1983_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___x_2004_;
goto v___jp_1950_;
}
}
}
}
v___jp_2007_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = lean_unsigned_to_nat(4u);
v___x_2024_ = l_Lean_Syntax_getArg(v___y_2008_, v___x_2023_);
lean_dec(v___y_2008_);
v___x_2025_ = l_Lean_Syntax_getOptional_x3f(v___x_2024_);
lean_dec(v___x_2024_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_box(0);
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2022_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___y_2016_;
v___y_1986_ = v___y_2015_;
v___y_1987_ = v___y_2012_;
v___y_1988_ = v_args_2014_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2013_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2009_;
v___y_1993_ = v___y_2020_;
v___y_1994_ = v___y_2018_;
v___y_1995_ = v___y_2021_;
v___y_1996_ = v___x_2026_;
goto v___jp_1981_;
}
else
{
lean_object* v_val_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_val_2027_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2025_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_val_2027_);
lean_dec(v___x_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_val_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2022_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___y_2016_;
v___y_1986_ = v___y_2015_;
v___y_1987_ = v___y_2012_;
v___y_1988_ = v_args_2014_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2013_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2009_;
v___y_1993_ = v___y_2020_;
v___y_1994_ = v___y_2018_;
v___y_1995_ = v___y_2021_;
v___y_1996_ = v___x_2032_;
goto v___jp_1981_;
}
}
}
}
v___jp_2036_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2051_ = lean_unsigned_to_nat(3u);
v___x_2052_ = l_Lean_Syntax_getArg(v___y_2039_, v___x_2051_);
v___x_2053_ = l_Lean_Syntax_isNone(v___x_2052_);
if (v___x_2053_ == 0)
{
uint8_t v___x_2054_; 
lean_inc(v___x_2052_);
v___x_2054_ = l_Lean_Syntax_matchesNull(v___x_2052_, v___x_2035_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v___x_2052_);
lean_dec(v_o_2042_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2056_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_1236_);
lean_dec(v___x_2052_);
v___x_2057_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc_ref(v___x_1222_);
v___x_2058_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_2057_);
lean_inc(v___x_2056_);
v___x_2059_ = l_Lean_Syntax_isOfKind(v___x_2056_, v___x_2058_);
lean_dec(v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec(v___x_2056_);
lean_dec(v_o_2042_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; lean_object* v_args_2062_; lean_object* v___x_2063_; 
v___x_2061_ = l_Lean_Syntax_getArg(v___x_2056_, v___x_2035_);
lean_dec(v___x_2056_);
v_args_2062_ = l_Lean_Syntax_getArgs(v___x_2061_);
lean_dec(v___x_2061_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_args_2062_);
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2038_;
v___y_2010_ = v___y_2037_;
v___y_2011_ = v___y_2040_;
v___y_2012_ = v_o_2042_;
v___y_2013_ = v___y_2041_;
v_args_2014_ = v___x_2063_;
v___y_2015_ = v___y_2043_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v___y_2019_ = v___y_2047_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
goto v___jp_2007_;
}
}
}
else
{
lean_object* v___x_2064_; 
lean_dec(v___x_2052_);
v___x_2064_ = lean_box(0);
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2038_;
v___y_2010_ = v___y_2037_;
v___y_2011_ = v___y_2040_;
v___y_2012_ = v_o_2042_;
v___y_2013_ = v___y_2041_;
v_args_2014_ = v___x_2064_;
v___y_2015_ = v___y_2043_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v___y_2019_ = v___y_2047_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
goto v___jp_2007_;
}
}
v___jp_2065_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2075_ = lean_unsigned_to_nat(2u);
v___x_2076_ = l_Lean_Syntax_getArg(v_stx_1220_, v___x_2075_);
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc_ref(v___x_1222_);
v___x_2078_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_2077_);
lean_inc(v___x_2076_);
v___x_2079_ = l_Lean_Syntax_isOfKind(v___x_2076_, v___x_2078_);
lean_dec(v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec(v___x_2076_);
lean_dec(v_bang_2066_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2080_;
}
else
{
lean_object* v_cfg_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_cfg_2081_ = l_Lean_Syntax_getArg(v___x_2076_, v___x_1236_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc_ref(v___x_1222_);
v___x_2083_ = l_Lean_Name_mkStr4(v___x_1222_, v___x_1223_, v___x_1224_, v___x_2082_);
lean_inc(v_cfg_2081_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v_cfg_2081_, v___x_2083_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v_cfg_2081_);
lean_dec(v___x_2076_);
lean_dec(v_bang_2066_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2086_ = l_Lean_Syntax_getArg(v___x_2076_, v___x_2035_);
v___x_2087_ = l_Lean_Syntax_getArg(v___x_2076_, v___x_2075_);
v___x_2088_ = l_Lean_Syntax_isNone(v___x_2087_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
lean_inc(v___x_2087_);
v___x_2089_ = l_Lean_Syntax_matchesNull(v___x_2087_, v___x_2035_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_dec(v_cfg_2081_);
lean_dec(v___x_2076_);
lean_dec(v_bang_2066_);
lean_dec(v_tk_1237_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v_o_2091_; lean_object* v___x_2092_; 
v_o_2091_ = l_Lean_Syntax_getArg(v___x_2087_, v___x_1236_);
lean_dec(v___x_2087_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_o_2091_);
v___y_2037_ = v_cfg_2081_;
v___y_2038_ = v___x_2086_;
v___y_2039_ = v___x_2076_;
v___y_2040_ = v_bang_2066_;
v___y_2041_ = v___x_2084_;
v_o_2042_ = v___x_2092_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2068_;
v___y_2045_ = v___y_2069_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2071_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
goto v___jp_2036_;
}
}
else
{
lean_object* v___x_2093_; 
lean_dec(v___x_2087_);
v___x_2093_ = lean_box(0);
v___y_2037_ = v_cfg_2081_;
v___y_2038_ = v___x_2086_;
v___y_2039_ = v___x_2076_;
v___y_2040_ = v_bang_2066_;
v___y_2041_ = v___x_2084_;
v_o_2042_ = v___x_2093_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2068_;
v___y_2045_ = v___y_2069_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2071_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
goto v___jp_2036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2101_, lean_object* v_stx_2102_, lean_object* v___x_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v___f_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v___x_40485__boxed_2117_; uint8_t v___x_40486__boxed_2118_; lean_object* v_res_2119_; 
v___x_40485__boxed_2117_ = lean_unbox(v___x_2101_);
v___x_40486__boxed_2118_ = lean_unbox(v___x_2103_);
v_res_2119_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40485__boxed_2117_, v_stx_2102_, v___x_40486__boxed_2118_, v___x_2104_, v___x_2105_, v___x_2106_, v___f_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_stx_2102_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___y_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2129_);
v___x_2143_ = l_Lean_Syntax_isOfKind(v_stx_2129_, v___x_2142_);
v___x_2144_ = 1;
v___f_2145_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2146_ = lean_box(v___x_2143_);
v___x_2147_ = lean_box(v___x_2144_);
v___y_2148_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2148_, 0, v___x_2146_);
lean_closure_set(v___y_2148_, 1, v_stx_2129_);
lean_closure_set(v___y_2148_, 2, v___x_2147_);
lean_closure_set(v___y_2148_, 3, v___x_2139_);
lean_closure_set(v___y_2148_, 4, v___x_2140_);
lean_closure_set(v___y_2148_, 5, v___x_2141_);
lean_closure_set(v___y_2148_, 6, v___f_2145_);
v___x_2149_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2149_, 0, v___y_2148_);
v___x_2150_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2149_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2162_, lean_object* v_as_2163_, lean_object* v_as_x27_2164_, lean_object* v_b_2165_, lean_object* v_a_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2162_, v_as_x27_2164_, v_b_2165_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2177_, lean_object* v_as_2178_, lean_object* v_as_x27_2179_, lean_object* v_b_2180_, lean_object* v_a_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2177_, v_as_2178_, v_as_x27_2179_, v_b_2180_, v_a_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v_as_x27_2179_);
lean_dec(v_as_2178_);
lean_dec(v___x_2177_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2192_, lean_object* v_ref_2193_, lean_object* v_msg_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2193_, v_msg_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_ref_2206_, lean_object* v_msg_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2205_, v_ref_2206_, v_msg_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v_ref_2206_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2218_, lean_object* v_ref_2219_, lean_object* v_constName_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2219_, v_constName_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_ref_2232_, lean_object* v_constName_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2231_, v_ref_2232_, v_constName_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v_ref_2232_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2244_, lean_object* v_msg_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2245_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_msg_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2256_, v_msg_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2268_, v___y_2275_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_opt_2279_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2290_, lean_object* v_ref_2291_, lean_object* v_msg_2292_, lean_object* v_declHint_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2291_, v_msg_2292_, v_declHint_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2304_, lean_object* v_ref_2305_, lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2304_, v_ref_2305_, v_msg_2306_, v_declHint_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v_ref_2305_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2318_, lean_object* v_declHint_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2318_, v_declHint_2319_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2330_, v_declHint_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2342_, lean_object* v_msgData_2343_, uint8_t v_severity_2344_, uint8_t v_isSilent_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2342_, v_msgData_2343_, v_severity_2344_, v_isSilent_2345_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2356_, lean_object* v_msgData_2357_, lean_object* v_severity_2358_, lean_object* v_isSilent_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_severity_boxed_2369_; uint8_t v_isSilent_boxed_2370_; lean_object* v_res_2371_; 
v_severity_boxed_2369_ = lean_unbox(v_severity_2358_);
v_isSilent_boxed_2370_ = lean_unbox(v_isSilent_2359_);
v_res_2371_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2356_, v_msgData_2357_, v_severity_boxed_2369_, v_isSilent_boxed_2370_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v_ref_2356_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2379_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2380_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2382_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2383_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2379_, v___x_2380_, v___x_2381_, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2414_ = l_Lean_addBuiltinDeclarationRanges(v___x_2412_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2417_, lean_object* v_as_x27_2418_, lean_object* v_b_2419_, lean_object* v___y_2420_){
_start:
{
if (lean_obj_tag(v_as_x27_2418_) == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_b_2419_);
return v___x_2422_;
}
else
{
lean_object* v_head_2423_; lean_object* v_tail_2424_; lean_object* v_ref_2425_; uint8_t v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_head_2423_ = lean_ctor_get(v_as_x27_2418_, 0);
v_tail_2424_ = lean_ctor_get(v_as_x27_2418_, 1);
v_ref_2425_ = lean_ctor_get(v___y_2420_, 5);
v___x_2426_ = 1;
v___x_2427_ = 0;
v___x_2428_ = l_Lean_SourceInfo_fromRef(v_ref_2425_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2430_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2431_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2428_);
v___x_2432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2428_);
lean_ctor_set(v___x_2432_, 1, v___x_2430_);
lean_ctor_set(v___x_2432_, 2, v___x_2431_);
lean_inc(v_head_2423_);
v___x_2433_ = l_Lean_mkCIdentFrom(v___x_2417_, v_head_2423_, v___x_2426_);
lean_inc_ref(v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node3(v___x_2428_, v___x_2429_, v___x_2432_, v___x_2432_, v___x_2433_);
v___x_2435_ = lean_array_push(v_b_2419_, v___x_2434_);
v_as_x27_2418_ = v_tail_2424_;
v_b_2419_ = v___x_2435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2437_, lean_object* v_as_x27_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2437_, v_as_x27_2438_, v_b_2439_, v___y_2440_);
lean_dec_ref(v___y_2440_);
lean_dec(v_as_x27_2438_);
lean_dec(v___x_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2443_, size_t v_sz_2444_, size_t v_i_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_lt(v_i_2445_, v_sz_2444_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_b_2446_);
return v___x_2457_;
}
else
{
lean_object* v_a_2458_; lean_object* v_name_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_a_2458_ = lean_array_uget_borrowed(v_as_2443_, v_i_2445_);
v_name_2459_ = lean_ctor_get(v_a_2458_, 0);
lean_inc(v_name_2459_);
v___x_2460_ = l_Lean_mkIdent(v_name_2459_);
lean_inc(v___x_2460_);
v___x_2461_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2460_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2463_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2460_, v_a_2462_, v_b_2446_, v___y_2453_);
lean_dec(v_a_2462_);
lean_dec(v___x_2460_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; size_t v___x_2465_; size_t v___x_2466_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = ((size_t)1ULL);
v___x_2466_ = lean_usize_add(v_i_2445_, v___x_2465_);
v_i_2445_ = v___x_2466_;
v_b_2446_ = v_a_2464_;
goto _start;
}
else
{
return v___x_2463_;
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v___x_2460_);
lean_dec_ref(v_b_2446_);
v_a_2468_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2461_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2461_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
size_t v_sz_boxed_2489_; size_t v_i_boxed_2490_; lean_object* v_res_2491_; 
v_sz_boxed_2489_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2490_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2476_, v_sz_boxed_2489_, v_i_boxed_2490_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_as_2476_);
return v_res_2491_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2495_);
return v___x_2497_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_unsigned_to_nat(32u);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = ((size_t)5ULL);
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_unsigned_to_nat(32u);
v___x_2504_ = lean_mk_empty_array_with_capacity(v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2506_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
lean_ctor_set(v___x_2506_, 2, v___x_2502_);
lean_ctor_set(v___x_2506_, 3, v___x_2502_);
lean_ctor_set_usize(v___x_2506_, 4, v___x_2501_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2508_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_ctor_set(v___x_2509_, 2, v___x_2508_);
lean_ctor_set(v___x_2509_, 3, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2511_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2521_, lean_object* v_stx_2522_, uint8_t v___x_2523_, lean_object* v___x_2524_, lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v___f_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
if (v___x_2521_ == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_2537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v_tk_2539_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2654_; uint8_t v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; lean_object* v_stxForSuggestion_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; uint8_t v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2718_; uint8_t v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___y_2747_; lean_object* v___y_2748_; uint8_t v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; uint8_t v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; uint8_t v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; uint8_t v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; lean_object* v___y_2899_; uint8_t v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; uint8_t v___y_2956_; lean_object* v___y_2957_; uint8_t v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; uint8_t v___y_2968_; lean_object* v___y_2994_; uint8_t v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v_stxForExecution_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; uint8_t v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; uint8_t v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3273_; uint8_t v___y_3274_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; uint8_t v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___y_3344_; uint8_t v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v_argsArray_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_args_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___x_3505_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_o_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v_bang_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_2538_ = lean_unsigned_to_nat(0u);
v_tk_2539_ = l_Lean_Syntax_getArg(v_stx_2522_, v___x_2538_);
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3564_ = l_Lean_Syntax_getArg(v_stx_2522_, v___x_3505_);
v___x_3565_ = l_Lean_Syntax_isNone(v___x_3564_);
if (v___x_3565_ == 0)
{
uint8_t v___x_3566_; 
lean_inc(v___x_3564_);
v___x_3566_ = l_Lean_Syntax_matchesNull(v___x_3564_, v___x_3505_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec(v___x_3564_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3567_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3567_;
}
else
{
lean_object* v_bang_3568_; lean_object* v___x_3569_; 
v_bang_3568_ = l_Lean_Syntax_getArg(v___x_3564_, v___x_2538_);
lean_dec(v___x_3564_);
v___x_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_bang_3568_);
v_bang_3536_ = v___x_3569_;
v___y_3537_ = v___y_2528_;
v___y_3538_ = v___y_2529_;
v___y_3539_ = v___y_2530_;
v___y_3540_ = v___y_2531_;
v___y_3541_ = v___y_2532_;
v___y_3542_ = v___y_2533_;
v___y_3543_ = v___y_2534_;
v___y_3544_ = v___y_2535_;
goto v___jp_3535_;
}
}
else
{
lean_object* v___x_3570_; 
lean_dec(v___x_3564_);
v___x_3570_ = lean_box(0);
v_bang_3536_ = v___x_3570_;
v___y_3537_ = v___y_2528_;
v___y_3538_ = v___y_2529_;
v___y_3539_ = v___y_2530_;
v___y_3540_ = v___y_2531_;
v___y_3541_ = v___y_2532_;
v___y_3542_ = v___y_2533_;
v___y_3543_ = v___y_2534_;
v___y_3544_ = v___y_2535_;
goto v___jp_3535_;
}
v___jp_2540_:
{
lean_object* v_usedTheorems_2547_; lean_object* v_diag_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2590_; 
v_usedTheorems_2547_ = lean_ctor_get(v___y_2541_, 0);
v_diag_2548_ = lean_ctor_get(v___y_2541_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___y_2541_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2550_ = v___y_2541_;
v_isShared_2551_ = v_isSharedCheck_2590_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_diag_2548_);
lean_inc(v_usedTheorems_2547_);
lean_dec(v___y_2541_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2590_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2542_, v_usedTheorems_2547_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec_ref(v_usedTheorems_2547_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_ref_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_ref_2554_ = lean_ctor_get(v___y_2545_, 5);
v___x_2555_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v_a_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2555_);
v___x_2557_ = v___x_2550_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_a_2553_);
v___x_2557_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_ctor_set(v___x_2559_, 2, v___x_2558_);
lean_ctor_set(v___x_2559_, 3, v___x_2558_);
lean_ctor_set(v___x_2559_, 4, v___x_2558_);
lean_ctor_set(v___x_2559_, 5, v___x_2558_);
lean_inc(v_ref_2554_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_ref_2554_);
v___x_2561_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2562_ = 4;
v___x_2563_ = l_Lean_MessageData_nil;
v___x_2564_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2539_, v___x_2559_, v___x_2560_, v___x_2561_, v___x_2558_, v___x_2562_, v___x_2563_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; 
v_unused_2572_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2572_);
v___x_2566_ = v___x_2564_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_dec(v___x_2564_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v_diag_2548_);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_diag_2548_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec_ref(v_diag_2548_);
v_a_2573_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2564_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2564_);
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
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2550_);
lean_dec_ref(v_diag_2548_);
lean_dec(v_tk_2539_);
v_a_2582_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2552_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2552_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
v___jp_2591_:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2595_, v___y_2592_, v___y_2597_, v___y_2596_, v___y_2594_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2603_ = l_Lean_Meta_simpAll(v_a_2601_, v___y_2599_, v___y_2598_, v___x_2602_, v___y_2592_, v___y_2597_, v___y_2596_, v___y_2594_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v_fst_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v_fst_2605_ = lean_ctor_get(v_a_2604_, 0);
if (lean_obj_tag(v_fst_2605_) == 0)
{
lean_object* v_snd_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_snd_2606_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_a_2604_);
v___x_2607_ = lean_box(0);
v___x_2608_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2607_, v___y_2595_, v___y_2592_, v___y_2597_, v___y_2596_, v___y_2594_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_dec_ref_known(v___x_2608_, 1);
v___y_2541_ = v_snd_2606_;
v___y_2542_ = v___y_2593_;
v___y_2543_ = v___y_2592_;
v___y_2544_ = v___y_2597_;
v___y_2545_ = v___y_2596_;
v___y_2546_ = v___y_2594_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_snd_2606_);
lean_dec(v___y_2593_);
lean_dec(v_tk_2539_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2635_; 
lean_inc_ref(v_fst_2605_);
v_snd_2617_ = lean_ctor_get(v_a_2604_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v_a_2604_, 0);
lean_dec(v_unused_2636_);
v___x_2619_ = v_a_2604_;
v_isShared_2620_ = v_isSharedCheck_2635_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_dec(v_a_2604_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2635_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_val_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v_val_2621_ = lean_ctor_get(v_fst_2605_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v_fst_2605_, 1);
v___x_2622_ = lean_box(0);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
lean_ctor_set(v___x_2619_, 1, v___x_2622_);
lean_ctor_set(v___x_2619_, 0, v_val_2621_);
v___x_2624_ = v___x_2619_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_val_2621_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2624_, v___y_2595_, v___y_2592_, v___y_2597_, v___y_2596_, v___y_2594_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_dec_ref_known(v___x_2625_, 1);
v___y_2541_ = v_snd_2617_;
v___y_2542_ = v___y_2593_;
v___y_2543_ = v___y_2592_;
v___y_2544_ = v___y_2597_;
v___y_2545_ = v___y_2596_;
v___y_2546_ = v___y_2594_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_snd_2617_);
lean_dec(v___y_2593_);
lean_dec(v_tk_2539_);
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v___y_2593_);
lean_dec(v_tk_2539_);
v_a_2637_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2603_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2603_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2593_);
lean_dec(v_tk_2539_);
v_a_2645_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2600_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2600_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
v___jp_2653_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2668_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2654_, v___x_2523_, v___y_2655_, v___x_2523_, v___x_2667_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2654_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
if (lean_obj_tag(v___y_2657_) == 0)
{
lean_object* v_ctx_2670_; lean_object* v_simprocs_2671_; 
v_ctx_2670_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_ctx_2670_);
v_simprocs_2671_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_simprocs_2671_);
lean_dec(v_a_2669_);
v___y_2592_ = v___y_2663_;
v___y_2593_ = v_stxForSuggestion_2658_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2660_;
v___y_2596_ = v___y_2665_;
v___y_2597_ = v___y_2664_;
v___y_2598_ = v_simprocs_2671_;
v___y_2599_ = v_ctx_2670_;
goto v___jp_2591_;
}
else
{
lean_dec_ref_known(v___y_2657_, 1);
if (v___y_2656_ == 0)
{
lean_object* v_ctx_2672_; lean_object* v_simprocs_2673_; 
v_ctx_2672_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_ctx_2672_);
v_simprocs_2673_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_simprocs_2673_);
lean_dec(v_a_2669_);
v___y_2592_ = v___y_2663_;
v___y_2593_ = v_stxForSuggestion_2658_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2660_;
v___y_2596_ = v___y_2665_;
v___y_2597_ = v___y_2664_;
v___y_2598_ = v_simprocs_2673_;
v___y_2599_ = v_ctx_2672_;
goto v___jp_2591_;
}
else
{
lean_object* v_ctx_2674_; lean_object* v_simprocs_2675_; lean_object* v___x_2676_; 
v_ctx_2674_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_ctx_2674_);
v_simprocs_2675_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_simprocs_2675_);
lean_dec(v_a_2669_);
v___x_2676_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2674_);
v___y_2592_ = v___y_2663_;
v___y_2593_ = v_stxForSuggestion_2658_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2660_;
v___y_2596_ = v___y_2665_;
v___y_2597_ = v___y_2664_;
v___y_2598_ = v_simprocs_2675_;
v___y_2599_ = v___x_2676_;
goto v___jp_2591_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_stxForSuggestion_2658_);
lean_dec(v___y_2657_);
lean_dec(v_tk_2539_);
v_a_2677_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2668_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2668_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
v___jp_2685_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc_ref_n(v___y_2699_, 2);
v___x_2706_ = l_Array_append___redArg(v___y_2699_, v___y_2705_);
lean_dec_ref(v___y_2705_);
lean_inc_n(v___y_2688_, 2);
lean_inc_n(v___y_2686_, 2);
v___x_2707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2686_);
lean_ctor_set(v___x_2707_, 1, v___y_2688_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2708_, 0, v___y_2686_);
lean_ctor_set(v___x_2708_, 1, v___y_2688_);
lean_ctor_set(v___x_2708_, 2, v___y_2699_);
v___x_2709_ = l_Lean_Syntax_node5(v___y_2686_, v___y_2698_, v___y_2696_, v___y_2703_, v___y_2693_, v___x_2707_, v___x_2708_);
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___y_2692_;
v___y_2656_ = v___y_2695_;
v___y_2657_ = v___y_2694_;
v_stxForSuggestion_2658_ = v___x_2709_;
v___y_2659_ = v___y_2697_;
v___y_2660_ = v___y_2701_;
v___y_2661_ = v___y_2691_;
v___y_2662_ = v___y_2690_;
v___y_2663_ = v___y_2689_;
v___y_2664_ = v___y_2704_;
v___y_2665_ = v___y_2702_;
v___y_2666_ = v___y_2700_;
goto v___jp_2653_;
}
v___jp_2710_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc_ref(v___y_2724_);
v___x_2731_ = l_Array_append___redArg(v___y_2724_, v___y_2730_);
lean_dec_ref(v___y_2730_);
lean_inc(v___y_2713_);
lean_inc(v___y_2711_);
v___x_2732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2732_, 0, v___y_2711_);
lean_ctor_set(v___x_2732_, 1, v___y_2713_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
if (lean_obj_tag(v___y_2721_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_val_2733_ = lean_ctor_get(v___y_2721_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v___y_2721_, 1);
v___x_2734_ = l_Lean_SourceInfo_fromRef(v_val_2733_, v___x_2523_);
lean_dec(v_val_2733_);
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Array_mkArray1___redArg(v___x_2736_);
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___y_2712_;
v___y_2688_ = v___y_2713_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___x_2732_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___y_2719_;
v___y_2696_ = v___y_2720_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___y_2723_;
v___y_2699_ = v___y_2724_;
v___y_2700_ = v___y_2725_;
v___y_2701_ = v___y_2726_;
v___y_2702_ = v___y_2728_;
v___y_2703_ = v___y_2727_;
v___y_2704_ = v___y_2729_;
v___y_2705_ = v___x_2737_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v___y_2721_);
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___y_2712_;
v___y_2688_ = v___y_2713_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___x_2732_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___y_2719_;
v___y_2696_ = v___y_2720_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___y_2723_;
v___y_2699_ = v___y_2724_;
v___y_2700_ = v___y_2725_;
v___y_2701_ = v___y_2726_;
v___y_2702_ = v___y_2728_;
v___y_2703_ = v___y_2727_;
v___y_2704_ = v___y_2729_;
v___y_2705_ = v___x_2738_;
goto v___jp_2685_;
}
}
v___jp_2739_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_inc_ref_n(v___y_2742_, 2);
v___x_2761_ = l_Array_append___redArg(v___y_2742_, v___y_2760_);
lean_dec_ref(v___y_2760_);
lean_inc_n(v___y_2745_, 3);
lean_inc_n(v___y_2752_, 5);
v___x_2762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2752_);
lean_ctor_set(v___x_2762_, 1, v___y_2745_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
v___x_2763_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___y_2752_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2766_ = l_Lean_Syntax_SepArray_ofElems(v___x_2765_, v___y_2758_);
lean_dec_ref(v___y_2758_);
v___x_2767_ = l_Array_append___redArg(v___y_2742_, v___x_2766_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___y_2752_);
lean_ctor_set(v___x_2768_, 1, v___y_2745_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
v___x_2769_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2752_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = l_Lean_Syntax_node3(v___y_2752_, v___y_2745_, v___x_2764_, v___x_2768_, v___x_2770_);
v___x_2772_ = l_Lean_Syntax_node5(v___y_2752_, v___y_2753_, v___y_2754_, v___y_2757_, v___y_2743_, v___x_2762_, v___x_2771_);
v___y_2654_ = v___y_2740_;
v___y_2655_ = v___y_2747_;
v___y_2656_ = v___y_2749_;
v___y_2657_ = v___y_2748_;
v_stxForSuggestion_2658_ = v___x_2772_;
v___y_2659_ = v___y_2750_;
v___y_2660_ = v___y_2755_;
v___y_2661_ = v___y_2746_;
v___y_2662_ = v___y_2744_;
v___y_2663_ = v___y_2741_;
v___y_2664_ = v___y_2759_;
v___y_2665_ = v___y_2756_;
v___y_2666_ = v___y_2751_;
goto v___jp_2653_;
}
v___jp_2773_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_inc_ref(v___y_2776_);
v___x_2795_ = l_Array_append___redArg(v___y_2776_, v___y_2794_);
lean_dec_ref(v___y_2794_);
lean_inc(v___y_2778_);
lean_inc(v___y_2786_);
v___x_2796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___y_2786_);
lean_ctor_set(v___x_2796_, 1, v___y_2778_);
lean_ctor_set(v___x_2796_, 2, v___x_2795_);
if (lean_obj_tag(v___y_2783_) == 1)
{
lean_object* v_val_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_val_2797_ = lean_ctor_get(v___y_2783_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v___y_2783_, 1);
v___x_2798_ = l_Lean_SourceInfo_fromRef(v_val_2797_, v___x_2523_);
lean_dec(v_val_2797_);
v___x_2799_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Array_mkArray1___redArg(v___x_2800_);
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___x_2796_;
v___y_2744_ = v___y_2777_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2781_;
v___y_2749_ = v___y_2782_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___y_2789_;
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2787_;
v___y_2756_ = v___y_2791_;
v___y_2757_ = v___y_2790_;
v___y_2758_ = v___y_2792_;
v___y_2759_ = v___y_2793_;
v___y_2760_ = v___x_2801_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2802_; 
lean_dec(v___y_2783_);
v___x_2802_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___x_2796_;
v___y_2744_ = v___y_2777_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2781_;
v___y_2749_ = v___y_2782_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___y_2789_;
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2787_;
v___y_2756_ = v___y_2791_;
v___y_2757_ = v___y_2790_;
v___y_2758_ = v___y_2792_;
v___y_2759_ = v___y_2793_;
v___y_2760_ = v___x_2802_;
goto v___jp_2739_;
}
}
v___jp_2803_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_inc_ref_n(v___y_2822_, 2);
v___x_2825_ = l_Array_append___redArg(v___y_2822_, v___y_2824_);
lean_dec_ref(v___y_2824_);
lean_inc_n(v___y_2809_, 3);
lean_inc_n(v___y_2820_, 5);
v___x_2826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2826_, 0, v___y_2820_);
lean_ctor_set(v___x_2826_, 1, v___y_2809_);
lean_ctor_set(v___x_2826_, 2, v___x_2825_);
v___x_2827_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___y_2820_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2830_ = l_Lean_Syntax_SepArray_ofElems(v___x_2829_, v___y_2818_);
lean_dec_ref(v___y_2818_);
v___x_2831_ = l_Array_append___redArg(v___y_2822_, v___x_2830_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___y_2820_);
lean_ctor_set(v___x_2832_, 1, v___y_2809_);
lean_ctor_set(v___x_2832_, 2, v___x_2831_);
v___x_2833_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___y_2820_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l_Lean_Syntax_node3(v___y_2820_, v___y_2809_, v___x_2828_, v___x_2832_, v___x_2834_);
v___x_2836_ = l_Lean_Syntax_node5(v___y_2820_, v___y_2821_, v___y_2813_, v___y_2817_, v___y_2823_, v___x_2826_, v___x_2835_);
v___y_2654_ = v___y_2804_;
v___y_2655_ = v___y_2808_;
v___y_2656_ = v___y_2811_;
v___y_2657_ = v___y_2810_;
v_stxForSuggestion_2658_ = v___x_2836_;
v___y_2659_ = v___y_2812_;
v___y_2660_ = v___y_2815_;
v___y_2661_ = v___y_2807_;
v___y_2662_ = v___y_2806_;
v___y_2663_ = v___y_2805_;
v___y_2664_ = v___y_2819_;
v___y_2665_ = v___y_2816_;
v___y_2666_ = v___y_2814_;
goto v___jp_2653_;
}
v___jp_2837_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc_ref(v___y_2857_);
v___x_2859_ = l_Array_append___redArg(v___y_2857_, v___y_2858_);
lean_dec_ref(v___y_2858_);
lean_inc(v___y_2843_);
lean_inc(v___y_2856_);
v___x_2860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2856_);
lean_ctor_set(v___x_2860_, 1, v___y_2843_);
lean_ctor_set(v___x_2860_, 2, v___x_2859_);
if (lean_obj_tag(v___y_2846_) == 1)
{
lean_object* v_val_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_val_2861_ = lean_ctor_get(v___y_2846_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v___y_2846_, 1);
v___x_2862_ = l_Lean_SourceInfo_fromRef(v_val_2861_, v___x_2523_);
lean_dec(v_val_2861_);
v___x_2863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Array_mkArray1___redArg(v___x_2864_);
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___y_2842_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___y_2847_;
v___y_2813_ = v___y_2848_;
v___y_2814_ = v___y_2849_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___y_2852_;
v___y_2817_ = v___y_2851_;
v___y_2818_ = v___y_2853_;
v___y_2819_ = v___y_2855_;
v___y_2820_ = v___y_2856_;
v___y_2821_ = v___y_2854_;
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v___x_2865_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2866_; 
lean_dec(v___y_2846_);
v___x_2866_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___y_2842_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___y_2847_;
v___y_2813_ = v___y_2848_;
v___y_2814_ = v___y_2849_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___y_2852_;
v___y_2817_ = v___y_2851_;
v___y_2818_ = v___y_2853_;
v___y_2819_ = v___y_2855_;
v___y_2820_ = v___y_2856_;
v___y_2821_ = v___y_2854_;
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v___x_2866_;
goto v___jp_2803_;
}
}
v___jp_2867_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_inc_ref_n(v___y_2869_, 2);
v___x_2888_ = l_Array_append___redArg(v___y_2869_, v___y_2887_);
lean_dec_ref(v___y_2887_);
lean_inc_n(v___y_2880_, 2);
lean_inc_n(v___y_2878_, 2);
v___x_2889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2878_);
lean_ctor_set(v___x_2889_, 1, v___y_2880_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___y_2878_);
lean_ctor_set(v___x_2890_, 1, v___y_2880_);
lean_ctor_set(v___x_2890_, 2, v___y_2869_);
v___x_2891_ = l_Lean_Syntax_node5(v___y_2878_, v___y_2884_, v___y_2877_, v___y_2885_, v___y_2871_, v___x_2889_, v___x_2890_);
v___y_2654_ = v___y_2868_;
v___y_2655_ = v___y_2874_;
v___y_2656_ = v___y_2876_;
v___y_2657_ = v___y_2875_;
v_stxForSuggestion_2658_ = v___x_2891_;
v___y_2659_ = v___y_2879_;
v___y_2660_ = v___y_2882_;
v___y_2661_ = v___y_2873_;
v___y_2662_ = v___y_2872_;
v___y_2663_ = v___y_2870_;
v___y_2664_ = v___y_2886_;
v___y_2665_ = v___y_2883_;
v___y_2666_ = v___y_2881_;
goto v___jp_2653_;
}
v___jp_2892_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_inc_ref(v___y_2893_);
v___x_2913_ = l_Array_append___redArg(v___y_2893_, v___y_2912_);
lean_dec_ref(v___y_2912_);
lean_inc(v___y_2905_);
lean_inc(v___y_2903_);
v___x_2914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___y_2903_);
lean_ctor_set(v___x_2914_, 1, v___y_2905_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
if (lean_obj_tag(v___y_2901_) == 1)
{
lean_object* v_val_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_val_2915_ = lean_ctor_get(v___y_2901_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v___y_2901_, 1);
v___x_2916_ = l_Lean_SourceInfo_fromRef(v_val_2915_, v___x_2523_);
lean_dec(v_val_2915_);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Array_mkArray1___redArg(v___x_2918_);
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___x_2914_;
v___y_2872_ = v___y_2896_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2898_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___y_2906_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___y_2909_;
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2911_;
v___y_2887_ = v___x_2919_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2920_; 
lean_dec(v___y_2901_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___x_2914_;
v___y_2872_ = v___y_2896_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2898_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___y_2906_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___y_2909_;
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2911_;
v___y_2887_ = v___x_2920_;
goto v___jp_2867_;
}
}
v___jp_2921_:
{
lean_object* v_ref_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_ref_2938_ = lean_ctor_get(v___y_2934_, 5);
v___x_2939_ = l_Lean_SourceInfo_fromRef(v_ref_2938_, v___y_2937_);
v___x_2940_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2941_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_2940_);
v___x_2942_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_2943_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2946_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2935_) == 1)
{
lean_object* v_val_2947_; lean_object* v___x_2948_; 
v_val_2947_ = lean_ctor_get(v___y_2935_, 0);
lean_inc(v_val_2947_);
lean_dec_ref_known(v___y_2935_, 1);
v___x_2948_ = l_Array_mkArray1___redArg(v_val_2947_);
v___y_2711_ = v___x_2939_;
v___y_2712_ = v___y_2922_;
v___y_2713_ = v___x_2945_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___y_2925_;
v___y_2717_ = v___y_2926_;
v___y_2718_ = v___y_2927_;
v___y_2719_ = v___y_2928_;
v___y_2720_ = v___x_2944_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___y_2930_;
v___y_2723_ = v___x_2941_;
v___y_2724_ = v___x_2946_;
v___y_2725_ = v___y_2931_;
v___y_2726_ = v___y_2932_;
v___y_2727_ = v___y_2933_;
v___y_2728_ = v___y_2934_;
v___y_2729_ = v___y_2936_;
v___y_2730_ = v___x_2948_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2949_; 
lean_dec(v___y_2935_);
v___x_2949_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2711_ = v___x_2939_;
v___y_2712_ = v___y_2922_;
v___y_2713_ = v___x_2945_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___y_2925_;
v___y_2717_ = v___y_2926_;
v___y_2718_ = v___y_2927_;
v___y_2719_ = v___y_2928_;
v___y_2720_ = v___x_2944_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___y_2930_;
v___y_2723_ = v___x_2941_;
v___y_2724_ = v___x_2946_;
v___y_2725_ = v___y_2931_;
v___y_2726_ = v___y_2932_;
v___y_2727_ = v___y_2933_;
v___y_2728_ = v___y_2934_;
v___y_2729_ = v___y_2936_;
v___y_2730_ = v___x_2949_;
goto v___jp_2710_;
}
}
v___jp_2950_:
{
if (v___y_2968_ == 0)
{
lean_object* v_ref_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_ref_2969_ = lean_ctor_get(v___y_2964_, 5);
v___x_2970_ = l_Lean_SourceInfo_fromRef(v_ref_2969_, v___y_2968_);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2972_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_2971_);
v___x_2973_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2977_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2966_) == 1)
{
lean_object* v_val_2978_; lean_object* v___x_2979_; 
v_val_2978_ = lean_ctor_get(v___y_2966_, 0);
lean_inc(v_val_2978_);
lean_dec_ref_known(v___y_2966_, 1);
v___x_2979_ = l_Array_mkArray1___redArg(v_val_2978_);
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___x_2977_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___x_2976_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___y_2957_;
v___y_2782_ = v___y_2958_;
v___y_2783_ = v___y_2959_;
v___y_2784_ = v___y_2960_;
v___y_2785_ = v___y_2961_;
v___y_2786_ = v___x_2970_;
v___y_2787_ = v___y_2962_;
v___y_2788_ = v___x_2975_;
v___y_2789_ = v___x_2972_;
v___y_2790_ = v___y_2963_;
v___y_2791_ = v___y_2964_;
v___y_2792_ = v___y_2965_;
v___y_2793_ = v___y_2967_;
v___y_2794_ = v___x_2979_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v___y_2966_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___x_2977_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___x_2976_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___y_2957_;
v___y_2782_ = v___y_2958_;
v___y_2783_ = v___y_2959_;
v___y_2784_ = v___y_2960_;
v___y_2785_ = v___y_2961_;
v___y_2786_ = v___x_2970_;
v___y_2787_ = v___y_2962_;
v___y_2788_ = v___x_2975_;
v___y_2789_ = v___x_2972_;
v___y_2790_ = v___y_2963_;
v___y_2791_ = v___y_2964_;
v___y_2792_ = v___y_2965_;
v___y_2793_ = v___y_2967_;
v___y_2794_ = v___x_2980_;
goto v___jp_2773_;
}
}
else
{
lean_object* v_ref_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_ref_2981_ = lean_ctor_get(v___y_2964_, 5);
v___x_2982_ = l_Lean_SourceInfo_fromRef(v_ref_2981_, v___y_2954_);
v___x_2983_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2984_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_2983_);
v___x_2985_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2989_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2966_) == 1)
{
lean_object* v_val_2990_; lean_object* v___x_2991_; 
v_val_2990_ = lean_ctor_get(v___y_2966_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v___y_2966_, 1);
v___x_2991_ = l_Array_mkArray1___redArg(v_val_2990_);
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2955_;
v___y_2842_ = v___y_2956_;
v___y_2843_ = v___x_2988_;
v___y_2844_ = v___y_2957_;
v___y_2845_ = v___y_2958_;
v___y_2846_ = v___y_2959_;
v___y_2847_ = v___y_2960_;
v___y_2848_ = v___x_2987_;
v___y_2849_ = v___y_2961_;
v___y_2850_ = v___y_2962_;
v___y_2851_ = v___y_2963_;
v___y_2852_ = v___y_2964_;
v___y_2853_ = v___y_2965_;
v___y_2854_ = v___x_2984_;
v___y_2855_ = v___y_2967_;
v___y_2856_ = v___x_2982_;
v___y_2857_ = v___x_2989_;
v___y_2858_ = v___x_2991_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v___y_2966_);
v___x_2992_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2955_;
v___y_2842_ = v___y_2956_;
v___y_2843_ = v___x_2988_;
v___y_2844_ = v___y_2957_;
v___y_2845_ = v___y_2958_;
v___y_2846_ = v___y_2959_;
v___y_2847_ = v___y_2960_;
v___y_2848_ = v___x_2987_;
v___y_2849_ = v___y_2961_;
v___y_2850_ = v___y_2962_;
v___y_2851_ = v___y_2963_;
v___y_2852_ = v___y_2964_;
v___y_2853_ = v___y_2965_;
v___y_2854_ = v___x_2984_;
v___y_2855_ = v___y_2967_;
v___y_2856_ = v___x_2982_;
v___y_2857_ = v___x_2989_;
v___y_2858_ = v___x_2992_;
goto v___jp_2837_;
}
}
}
v___jp_2993_:
{
lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3010_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2994_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = lean_array_get_size(v___y_2998_);
v___x_3013_ = lean_nat_dec_eq(v___x_3012_, v___x_2538_);
if (v___x_3013_ == 0)
{
if (lean_obj_tag(v___y_2996_) == 0)
{
v___y_2951_ = v_stxForExecution_3001_;
v___y_2952_ = v___y_3006_;
v___y_2953_ = v___y_3005_;
v___y_2954_ = v___x_3013_;
v___y_2955_ = v___y_3004_;
v___y_2956_ = v___y_2995_;
v___y_2957_ = v___y_2996_;
v___y_2958_ = v___y_2997_;
v___y_2959_ = v___y_3000_;
v___y_2960_ = v___y_3002_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v___y_3003_;
v___y_2963_ = v_a_3011_;
v___y_2964_ = v___y_3008_;
v___y_2965_ = v___y_2998_;
v___y_2966_ = v___y_2999_;
v___y_2967_ = v___y_3007_;
v___y_2968_ = v___x_3013_;
goto v___jp_2950_;
}
else
{
v___y_2951_ = v_stxForExecution_3001_;
v___y_2952_ = v___y_3006_;
v___y_2953_ = v___y_3005_;
v___y_2954_ = v___x_3013_;
v___y_2955_ = v___y_3004_;
v___y_2956_ = v___y_2995_;
v___y_2957_ = v___y_2996_;
v___y_2958_ = v___y_2997_;
v___y_2959_ = v___y_3000_;
v___y_2960_ = v___y_3002_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v___y_3003_;
v___y_2963_ = v_a_3011_;
v___y_2964_ = v___y_3008_;
v___y_2965_ = v___y_2998_;
v___y_2966_ = v___y_2999_;
v___y_2967_ = v___y_3007_;
v___y_2968_ = v___y_2997_;
goto v___jp_2950_;
}
}
else
{
lean_dec_ref(v___y_2998_);
if (lean_obj_tag(v___y_2996_) == 0)
{
uint8_t v___x_3014_; 
v___x_3014_ = 0;
v___y_2922_ = v_stxForExecution_3001_;
v___y_2923_ = v___y_3006_;
v___y_2924_ = v___y_3005_;
v___y_2925_ = v___y_3004_;
v___y_2926_ = v___y_2995_;
v___y_2927_ = v___y_2996_;
v___y_2928_ = v___y_2997_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_3002_;
v___y_2931_ = v___y_3009_;
v___y_2932_ = v___y_3003_;
v___y_2933_ = v_a_3011_;
v___y_2934_ = v___y_3008_;
v___y_2935_ = v___y_2999_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___x_3014_;
goto v___jp_2921_;
}
else
{
if (v___y_2997_ == 0)
{
v___y_2922_ = v_stxForExecution_3001_;
v___y_2923_ = v___y_3006_;
v___y_2924_ = v___y_3005_;
v___y_2925_ = v___y_3004_;
v___y_2926_ = v___y_2995_;
v___y_2927_ = v___y_2996_;
v___y_2928_ = v___y_2997_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_3002_;
v___y_2931_ = v___y_3009_;
v___y_2932_ = v___y_3003_;
v___y_2933_ = v_a_3011_;
v___y_2934_ = v___y_3008_;
v___y_2935_ = v___y_2999_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_2997_;
goto v___jp_2921_;
}
else
{
lean_object* v_ref_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_ref_3015_ = lean_ctor_get(v___y_3008_, 5);
v___x_3016_ = 0;
v___x_3017_ = l_Lean_SourceInfo_fromRef(v_ref_3015_, v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3019_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3018_);
v___x_3020_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_3021_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3024_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2999_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3026_; 
v_val_3025_ = lean_ctor_get(v___y_2999_, 0);
lean_inc(v_val_3025_);
lean_dec_ref_known(v___y_2999_, 1);
v___x_3026_ = l_Array_mkArray1___redArg(v_val_3025_);
v___y_2893_ = v___x_3024_;
v___y_2894_ = v_stxForExecution_3001_;
v___y_2895_ = v___y_3006_;
v___y_2896_ = v___y_3005_;
v___y_2897_ = v___y_3004_;
v___y_2898_ = v___y_2995_;
v___y_2899_ = v___y_2996_;
v___y_2900_ = v___y_2997_;
v___y_2901_ = v___y_3000_;
v___y_2902_ = v___x_3022_;
v___y_2903_ = v___x_3017_;
v___y_2904_ = v___y_3002_;
v___y_2905_ = v___x_3023_;
v___y_2906_ = v___y_3009_;
v___y_2907_ = v___y_3003_;
v___y_2908_ = v_a_3011_;
v___y_2909_ = v___x_3019_;
v___y_2910_ = v___y_3008_;
v___y_2911_ = v___y_3007_;
v___y_2912_ = v___x_3026_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_3027_; 
lean_dec(v___y_2999_);
v___x_3027_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2893_ = v___x_3024_;
v___y_2894_ = v_stxForExecution_3001_;
v___y_2895_ = v___y_3006_;
v___y_2896_ = v___y_3005_;
v___y_2897_ = v___y_3004_;
v___y_2898_ = v___y_2995_;
v___y_2899_ = v___y_2996_;
v___y_2900_ = v___y_2997_;
v___y_2901_ = v___y_3000_;
v___y_2902_ = v___x_3022_;
v___y_2903_ = v___x_3017_;
v___y_2904_ = v___y_3002_;
v___y_2905_ = v___x_3023_;
v___y_2906_ = v___y_3009_;
v___y_2907_ = v___y_3003_;
v___y_2908_ = v_a_3011_;
v___y_2909_ = v___x_3019_;
v___y_2910_ = v___y_3008_;
v___y_2911_ = v___y_3007_;
v___y_2912_ = v___x_3027_;
goto v___jp_2892_;
}
}
}
}
}
v___jp_3028_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_inc_ref_n(v___y_3029_, 2);
v___x_3051_ = l_Array_append___redArg(v___y_3029_, v___y_3050_);
lean_dec_ref(v___y_3050_);
lean_inc_n(v___y_3049_, 2);
lean_inc_n(v___y_3030_, 2);
v___x_3052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3030_);
lean_ctor_set(v___x_3052_, 1, v___y_3049_);
lean_ctor_set(v___x_3052_, 2, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3030_);
lean_ctor_set(v___x_3053_, 1, v___y_3049_);
lean_ctor_set(v___x_3053_, 2, v___y_3029_);
lean_inc(v___y_3041_);
v___x_3054_ = l_Lean_Syntax_node5(v___y_3030_, v___y_3034_, v___y_3032_, v___y_3041_, v___y_3045_, v___x_3052_, v___x_3053_);
v___y_2994_ = v___y_3041_;
v___y_2995_ = v___y_3033_;
v___y_2996_ = v___y_3036_;
v___y_2997_ = v___y_3035_;
v___y_2998_ = v___y_3047_;
v___y_2999_ = v___y_3048_;
v___y_3000_ = v___y_3039_;
v_stxForExecution_3001_ = v___x_3054_;
v___y_3002_ = v___y_3040_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3046_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3037_;
v___y_3008_ = v___y_3031_;
v___y_3009_ = v___y_3042_;
goto v___jp_2993_;
}
v___jp_3055_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_inc_ref(v___y_3056_);
v___x_3077_ = l_Array_append___redArg(v___y_3056_, v___y_3076_);
lean_dec_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc(v___y_3057_);
v___x_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___y_3057_);
lean_ctor_set(v___x_3078_, 1, v___y_3075_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
if (lean_obj_tag(v___y_3066_) == 1)
{
lean_object* v_val_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_val_3079_ = lean_ctor_get(v___y_3066_, 0);
v___x_3080_ = l_Lean_SourceInfo_fromRef(v_val_3079_, v___x_2523_);
v___x_3081_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Array_mkArray1___redArg(v___x_3082_);
v___y_3029_ = v___y_3056_;
v___y_3030_ = v___y_3057_;
v___y_3031_ = v___y_3058_;
v___y_3032_ = v___y_3059_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3061_;
v___y_3035_ = v___y_3062_;
v___y_3036_ = v___y_3063_;
v___y_3037_ = v___y_3064_;
v___y_3038_ = v___y_3065_;
v___y_3039_ = v___y_3066_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3068_;
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___x_3078_;
v___y_3046_ = v___y_3072_;
v___y_3047_ = v___y_3073_;
v___y_3048_ = v___y_3074_;
v___y_3049_ = v___y_3075_;
v___y_3050_ = v___x_3083_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3029_ = v___y_3056_;
v___y_3030_ = v___y_3057_;
v___y_3031_ = v___y_3058_;
v___y_3032_ = v___y_3059_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3061_;
v___y_3035_ = v___y_3062_;
v___y_3036_ = v___y_3063_;
v___y_3037_ = v___y_3064_;
v___y_3038_ = v___y_3065_;
v___y_3039_ = v___y_3066_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3068_;
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___x_3078_;
v___y_3046_ = v___y_3072_;
v___y_3047_ = v___y_3073_;
v___y_3048_ = v___y_3074_;
v___y_3049_ = v___y_3075_;
v___y_3050_ = v___x_3084_;
goto v___jp_3028_;
}
}
v___jp_3085_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_inc_ref_n(v___y_3106_, 2);
v___x_3108_ = l_Array_append___redArg(v___y_3106_, v___y_3107_);
lean_dec_ref(v___y_3107_);
lean_inc_n(v___y_3088_, 3);
lean_inc_n(v___y_3092_, 5);
v___x_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3092_);
lean_ctor_set(v___x_3109_, 1, v___y_3088_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3092_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3113_ = l_Lean_Syntax_SepArray_ofElems(v___x_3112_, v___y_3103_);
v___x_3114_ = l_Array_append___redArg(v___y_3106_, v___x_3113_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___y_3092_);
lean_ctor_set(v___x_3115_, 1, v___y_3088_);
lean_ctor_set(v___x_3115_, 2, v___x_3114_);
v___x_3116_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___y_3092_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_Syntax_node3(v___y_3092_, v___y_3088_, v___x_3111_, v___x_3115_, v___x_3117_);
lean_inc(v___y_3098_);
v___x_3119_ = l_Lean_Syntax_node5(v___y_3092_, v___y_3093_, v___y_3104_, v___y_3098_, v___y_3097_, v___x_3109_, v___x_3118_);
v___y_2994_ = v___y_3098_;
v___y_2995_ = v___y_3087_;
v___y_2996_ = v___y_3090_;
v___y_2997_ = v___y_3089_;
v___y_2998_ = v___y_3103_;
v___y_2999_ = v___y_3105_;
v___y_3000_ = v___y_3095_;
v_stxForExecution_3001_ = v___x_3119_;
v___y_3002_ = v___y_3096_;
v___y_3003_ = v___y_3094_;
v___y_3004_ = v___y_3102_;
v___y_3005_ = v___y_3100_;
v___y_3006_ = v___y_3101_;
v___y_3007_ = v___y_3091_;
v___y_3008_ = v___y_3086_;
v___y_3009_ = v___y_3099_;
goto v___jp_2993_;
}
v___jp_3120_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_inc_ref(v___y_3140_);
v___x_3142_ = l_Array_append___redArg(v___y_3140_, v___y_3141_);
lean_dec_ref(v___y_3141_);
lean_inc(v___y_3123_);
lean_inc(v___y_3124_);
v___x_3143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3143_, 0, v___y_3124_);
lean_ctor_set(v___x_3143_, 1, v___y_3123_);
lean_ctor_set(v___x_3143_, 2, v___x_3142_);
if (lean_obj_tag(v___y_3130_) == 1)
{
lean_object* v_val_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_val_3144_ = lean_ctor_get(v___y_3130_, 0);
v___x_3145_ = l_Lean_SourceInfo_fromRef(v_val_3144_, v___x_2523_);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Array_mkArray1___redArg(v___x_3147_);
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___y_3123_;
v___y_3089_ = v___y_3125_;
v___y_3090_ = v___y_3126_;
v___y_3091_ = v___y_3127_;
v___y_3092_ = v___y_3124_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___x_3143_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3136_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___y_3137_;
v___y_3105_ = v___y_3139_;
v___y_3106_ = v___y_3140_;
v___y_3107_ = v___x_3148_;
goto v___jp_3085_;
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___y_3123_;
v___y_3089_ = v___y_3125_;
v___y_3090_ = v___y_3126_;
v___y_3091_ = v___y_3127_;
v___y_3092_ = v___y_3124_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___x_3143_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3136_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___y_3137_;
v___y_3105_ = v___y_3139_;
v___y_3106_ = v___y_3140_;
v___y_3107_ = v___x_3149_;
goto v___jp_3085_;
}
}
v___jp_3150_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_inc_ref_n(v___y_3152_, 2);
v___x_3173_ = l_Array_append___redArg(v___y_3152_, v___y_3172_);
lean_dec_ref(v___y_3172_);
lean_inc_n(v___y_3158_, 3);
lean_inc_n(v___y_3165_, 5);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3165_);
lean_ctor_set(v___x_3174_, 1, v___y_3158_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3165_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3178_ = l_Lean_Syntax_SepArray_ofElems(v___x_3177_, v___y_3169_);
v___x_3179_ = l_Array_append___redArg(v___y_3152_, v___x_3178_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3180_, 0, v___y_3165_);
lean_ctor_set(v___x_3180_, 1, v___y_3158_);
lean_ctor_set(v___x_3180_, 2, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___y_3165_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_Syntax_node3(v___y_3165_, v___y_3158_, v___x_3176_, v___x_3180_, v___x_3182_);
lean_inc(v___y_3162_);
v___x_3184_ = l_Lean_Syntax_node5(v___y_3165_, v___y_3151_, v___y_3164_, v___y_3162_, v___y_3171_, v___x_3174_, v___x_3183_);
v___y_2994_ = v___y_3162_;
v___y_2995_ = v___y_3154_;
v___y_2996_ = v___y_3156_;
v___y_2997_ = v___y_3155_;
v___y_2998_ = v___y_3169_;
v___y_2999_ = v___y_3170_;
v___y_3000_ = v___y_3160_;
v_stxForExecution_3001_ = v___x_3184_;
v___y_3002_ = v___y_3161_;
v___y_3003_ = v___y_3159_;
v___y_3004_ = v___y_3168_;
v___y_3005_ = v___y_3166_;
v___y_3006_ = v___y_3167_;
v___y_3007_ = v___y_3157_;
v___y_3008_ = v___y_3153_;
v___y_3009_ = v___y_3163_;
goto v___jp_2993_;
}
v___jp_3185_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc_ref(v___y_3187_);
v___x_3207_ = l_Array_append___redArg(v___y_3187_, v___y_3206_);
lean_dec_ref(v___y_3206_);
lean_inc(v___y_3190_);
lean_inc(v___y_3200_);
v___x_3208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3208_, 0, v___y_3200_);
lean_ctor_set(v___x_3208_, 1, v___y_3190_);
lean_ctor_set(v___x_3208_, 2, v___x_3207_);
if (lean_obj_tag(v___y_3195_) == 1)
{
lean_object* v_val_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_val_3209_ = lean_ctor_get(v___y_3195_, 0);
v___x_3210_ = l_Lean_SourceInfo_fromRef(v_val_3209_, v___x_2523_);
v___x_3211_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Array_mkArray1___redArg(v___x_3212_);
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3190_;
v___y_3159_ = v___y_3194_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3197_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___y_3200_;
v___y_3166_ = v___y_3201_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___y_3204_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___x_3208_;
v___y_3172_ = v___x_3213_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3214_; 
v___x_3214_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3190_;
v___y_3159_ = v___y_3194_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3197_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___y_3200_;
v___y_3166_ = v___y_3201_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___y_3204_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___x_3208_;
v___y_3172_ = v___x_3214_;
goto v___jp_3150_;
}
}
v___jp_3215_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc_ref_n(v___y_3222_, 2);
v___x_3238_ = l_Array_append___redArg(v___y_3222_, v___y_3237_);
lean_dec_ref(v___y_3237_);
lean_inc_n(v___y_3218_, 2);
lean_inc_n(v___y_3223_, 2);
v___x_3239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3239_, 0, v___y_3223_);
lean_ctor_set(v___x_3239_, 1, v___y_3218_);
lean_ctor_set(v___x_3239_, 2, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___y_3223_);
lean_ctor_set(v___x_3240_, 1, v___y_3218_);
lean_ctor_set(v___x_3240_, 2, v___y_3222_);
lean_inc(v___y_3228_);
v___x_3241_ = l_Lean_Syntax_node5(v___y_3223_, v___y_3216_, v___y_3230_, v___y_3228_, v___y_3235_, v___x_3239_, v___x_3240_);
v___y_2994_ = v___y_3228_;
v___y_2995_ = v___y_3219_;
v___y_2996_ = v___y_3221_;
v___y_2997_ = v___y_3220_;
v___y_2998_ = v___y_3234_;
v___y_2999_ = v___y_3236_;
v___y_3000_ = v___y_3226_;
v_stxForExecution_3001_ = v___x_3241_;
v___y_3002_ = v___y_3227_;
v___y_3003_ = v___y_3225_;
v___y_3004_ = v___y_3233_;
v___y_3005_ = v___y_3231_;
v___y_3006_ = v___y_3232_;
v___y_3007_ = v___y_3224_;
v___y_3008_ = v___y_3217_;
v___y_3009_ = v___y_3229_;
goto v___jp_2993_;
}
v___jp_3242_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_inc_ref(v___y_3247_);
v___x_3264_ = l_Array_append___redArg(v___y_3247_, v___y_3263_);
lean_dec_ref(v___y_3263_);
lean_inc(v___y_3245_);
lean_inc(v___y_3248_);
v___x_3265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3265_, 0, v___y_3248_);
lean_ctor_set(v___x_3265_, 1, v___y_3245_);
lean_ctor_set(v___x_3265_, 2, v___x_3264_);
if (lean_obj_tag(v___y_3253_) == 1)
{
lean_object* v_val_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_val_3266_ = lean_ctor_get(v___y_3253_, 0);
v___x_3267_ = l_Lean_SourceInfo_fromRef(v_val_3266_, v___x_2523_);
v___x_3268_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = l_Array_mkArray1___redArg(v___x_3269_);
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3246_;
v___y_3220_ = v___y_3249_;
v___y_3221_ = v___y_3250_;
v___y_3222_ = v___y_3247_;
v___y_3223_ = v___y_3248_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3256_;
v___y_3230_ = v___y_3258_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3259_;
v___y_3233_ = v___y_3260_;
v___y_3234_ = v___y_3261_;
v___y_3235_ = v___x_3265_;
v___y_3236_ = v___y_3262_;
v___y_3237_ = v___x_3270_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3271_; 
v___x_3271_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3246_;
v___y_3220_ = v___y_3249_;
v___y_3221_ = v___y_3250_;
v___y_3222_ = v___y_3247_;
v___y_3223_ = v___y_3248_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3256_;
v___y_3230_ = v___y_3258_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3259_;
v___y_3233_ = v___y_3260_;
v___y_3234_ = v___y_3261_;
v___y_3235_ = v___x_3265_;
v___y_3236_ = v___y_3262_;
v___y_3237_ = v___x_3271_;
goto v___jp_3215_;
}
}
v___jp_3272_:
{
lean_object* v_ref_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_ref_3289_ = lean_ctor_get(v___y_3273_, 5);
v___x_3290_ = l_Lean_SourceInfo_fromRef(v_ref_3289_, v___y_3288_);
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3292_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3291_);
v___x_3293_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_3294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3297_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3287_) == 1)
{
lean_object* v_val_3298_; lean_object* v___x_3299_; 
v_val_3298_ = lean_ctor_get(v___y_3287_, 0);
lean_inc(v_val_3298_);
v___x_3299_ = l_Array_mkArray1___redArg(v_val_3298_);
v___y_3056_ = v___x_3297_;
v___y_3057_ = v___x_3290_;
v___y_3058_ = v___y_3273_;
v___y_3059_ = v___x_3295_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___x_3292_;
v___y_3062_ = v___y_3275_;
v___y_3063_ = v___y_3276_;
v___y_3064_ = v___y_3277_;
v___y_3065_ = v___y_3278_;
v___y_3066_ = v___y_3279_;
v___y_3067_ = v___y_3280_;
v___y_3068_ = v___y_3281_;
v___y_3069_ = v___y_3282_;
v___y_3070_ = v___y_3283_;
v___y_3071_ = v___y_3284_;
v___y_3072_ = v___y_3285_;
v___y_3073_ = v___y_3286_;
v___y_3074_ = v___y_3287_;
v___y_3075_ = v___x_3296_;
v___y_3076_ = v___x_3299_;
goto v___jp_3055_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3056_ = v___x_3297_;
v___y_3057_ = v___x_3290_;
v___y_3058_ = v___y_3273_;
v___y_3059_ = v___x_3295_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___x_3292_;
v___y_3062_ = v___y_3275_;
v___y_3063_ = v___y_3276_;
v___y_3064_ = v___y_3277_;
v___y_3065_ = v___y_3278_;
v___y_3066_ = v___y_3279_;
v___y_3067_ = v___y_3280_;
v___y_3068_ = v___y_3281_;
v___y_3069_ = v___y_3282_;
v___y_3070_ = v___y_3283_;
v___y_3071_ = v___y_3284_;
v___y_3072_ = v___y_3285_;
v___y_3073_ = v___y_3286_;
v___y_3074_ = v___y_3287_;
v___y_3075_ = v___x_3296_;
v___y_3076_ = v___x_3300_;
goto v___jp_3055_;
}
}
v___jp_3301_:
{
if (v___y_3318_ == 0)
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_ref_3319_ = lean_ctor_get(v___y_3302_, 5);
v___x_3320_ = l_Lean_SourceInfo_fromRef(v_ref_3319_, v___y_3318_);
v___x_3321_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3322_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3321_);
v___x_3323_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3327_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3317_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v___y_3317_, 0);
lean_inc(v_val_3328_);
v___x_3329_ = l_Array_mkArray1___redArg(v_val_3328_);
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3303_;
v___y_3123_ = v___x_3326_;
v___y_3124_ = v___x_3320_;
v___y_3125_ = v___y_3304_;
v___y_3126_ = v___y_3305_;
v___y_3127_ = v___y_3306_;
v___y_3128_ = v___x_3322_;
v___y_3129_ = v___y_3307_;
v___y_3130_ = v___y_3308_;
v___y_3131_ = v___y_3309_;
v___y_3132_ = v___y_3310_;
v___y_3133_ = v___y_3311_;
v___y_3134_ = v___y_3313_;
v___y_3135_ = v___y_3314_;
v___y_3136_ = v___y_3315_;
v___y_3137_ = v___x_3325_;
v___y_3138_ = v___y_3316_;
v___y_3139_ = v___y_3317_;
v___y_3140_ = v___x_3327_;
v___y_3141_ = v___x_3329_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3303_;
v___y_3123_ = v___x_3326_;
v___y_3124_ = v___x_3320_;
v___y_3125_ = v___y_3304_;
v___y_3126_ = v___y_3305_;
v___y_3127_ = v___y_3306_;
v___y_3128_ = v___x_3322_;
v___y_3129_ = v___y_3307_;
v___y_3130_ = v___y_3308_;
v___y_3131_ = v___y_3309_;
v___y_3132_ = v___y_3310_;
v___y_3133_ = v___y_3311_;
v___y_3134_ = v___y_3313_;
v___y_3135_ = v___y_3314_;
v___y_3136_ = v___y_3315_;
v___y_3137_ = v___x_3325_;
v___y_3138_ = v___y_3316_;
v___y_3139_ = v___y_3317_;
v___y_3140_ = v___x_3327_;
v___y_3141_ = v___x_3330_;
goto v___jp_3120_;
}
}
else
{
lean_object* v_ref_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_ref_3331_ = lean_ctor_get(v___y_3302_, 5);
v___x_3332_ = l_Lean_SourceInfo_fromRef(v_ref_3331_, v___y_3312_);
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3334_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3333_);
v___x_3335_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3339_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3317_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3341_; 
v_val_3340_ = lean_ctor_get(v___y_3317_, 0);
lean_inc(v_val_3340_);
v___x_3341_ = l_Array_mkArray1___redArg(v_val_3340_);
v___y_3186_ = v___x_3334_;
v___y_3187_ = v___x_3339_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___x_3338_;
v___y_3191_ = v___y_3304_;
v___y_3192_ = v___y_3305_;
v___y_3193_ = v___y_3306_;
v___y_3194_ = v___y_3307_;
v___y_3195_ = v___y_3308_;
v___y_3196_ = v___y_3309_;
v___y_3197_ = v___y_3310_;
v___y_3198_ = v___x_3337_;
v___y_3199_ = v___y_3311_;
v___y_3200_ = v___x_3332_;
v___y_3201_ = v___y_3313_;
v___y_3202_ = v___y_3314_;
v___y_3203_ = v___y_3315_;
v___y_3204_ = v___y_3316_;
v___y_3205_ = v___y_3317_;
v___y_3206_ = v___x_3341_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3186_ = v___x_3334_;
v___y_3187_ = v___x_3339_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___x_3338_;
v___y_3191_ = v___y_3304_;
v___y_3192_ = v___y_3305_;
v___y_3193_ = v___y_3306_;
v___y_3194_ = v___y_3307_;
v___y_3195_ = v___y_3308_;
v___y_3196_ = v___y_3309_;
v___y_3197_ = v___y_3310_;
v___y_3198_ = v___x_3337_;
v___y_3199_ = v___y_3311_;
v___y_3200_ = v___x_3332_;
v___y_3201_ = v___y_3313_;
v___y_3202_ = v___y_3314_;
v___y_3203_ = v___y_3315_;
v___y_3204_ = v___y_3316_;
v___y_3205_ = v___y_3317_;
v___y_3206_ = v___x_3342_;
goto v___jp_3185_;
}
}
}
v___jp_3343_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = lean_array_get_size(v_argsArray_3350_);
v___x_3360_ = lean_nat_dec_eq(v___x_3359_, v___x_2538_);
if (v___x_3360_ == 0)
{
if (lean_obj_tag(v___y_3347_) == 0)
{
v___y_3302_ = v___y_3357_;
v___y_3303_ = v___y_3345_;
v___y_3304_ = v___y_3346_;
v___y_3305_ = v___y_3347_;
v___y_3306_ = v___y_3356_;
v___y_3307_ = v___y_3352_;
v___y_3308_ = v___y_3348_;
v___y_3309_ = v___y_3351_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v___y_3358_;
v___y_3312_ = v___x_3360_;
v___y_3313_ = v___y_3354_;
v___y_3314_ = v___y_3355_;
v___y_3315_ = v___y_3353_;
v___y_3316_ = v_argsArray_3350_;
v___y_3317_ = v___y_3349_;
v___y_3318_ = v___x_3360_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___y_3357_;
v___y_3303_ = v___y_3345_;
v___y_3304_ = v___y_3346_;
v___y_3305_ = v___y_3347_;
v___y_3306_ = v___y_3356_;
v___y_3307_ = v___y_3352_;
v___y_3308_ = v___y_3348_;
v___y_3309_ = v___y_3351_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v___y_3358_;
v___y_3312_ = v___x_3360_;
v___y_3313_ = v___y_3354_;
v___y_3314_ = v___y_3355_;
v___y_3315_ = v___y_3353_;
v___y_3316_ = v_argsArray_3350_;
v___y_3317_ = v___y_3349_;
v___y_3318_ = v___y_3346_;
goto v___jp_3301_;
}
}
else
{
if (lean_obj_tag(v___y_3347_) == 0)
{
uint8_t v___x_3361_; 
v___x_3361_ = 0;
v___y_3273_ = v___y_3357_;
v___y_3274_ = v___y_3345_;
v___y_3275_ = v___y_3346_;
v___y_3276_ = v___y_3347_;
v___y_3277_ = v___y_3356_;
v___y_3278_ = v___y_3352_;
v___y_3279_ = v___y_3348_;
v___y_3280_ = v___y_3351_;
v___y_3281_ = v___y_3344_;
v___y_3282_ = v___y_3358_;
v___y_3283_ = v___y_3354_;
v___y_3284_ = v___y_3355_;
v___y_3285_ = v___y_3353_;
v___y_3286_ = v_argsArray_3350_;
v___y_3287_ = v___y_3349_;
v___y_3288_ = v___x_3361_;
goto v___jp_3272_;
}
else
{
if (v___y_3346_ == 0)
{
v___y_3273_ = v___y_3357_;
v___y_3274_ = v___y_3345_;
v___y_3275_ = v___y_3346_;
v___y_3276_ = v___y_3347_;
v___y_3277_ = v___y_3356_;
v___y_3278_ = v___y_3352_;
v___y_3279_ = v___y_3348_;
v___y_3280_ = v___y_3351_;
v___y_3281_ = v___y_3344_;
v___y_3282_ = v___y_3358_;
v___y_3283_ = v___y_3354_;
v___y_3284_ = v___y_3355_;
v___y_3285_ = v___y_3353_;
v___y_3286_ = v_argsArray_3350_;
v___y_3287_ = v___y_3349_;
v___y_3288_ = v___y_3346_;
goto v___jp_3272_;
}
else
{
lean_object* v_ref_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_ref_3362_ = lean_ctor_get(v___y_3357_, 5);
v___x_3363_ = 0;
v___x_3364_ = l_Lean_SourceInfo_fromRef(v_ref_3362_, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3366_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3365_);
v___x_3367_ = l_Lean_SourceInfo_fromRef(v_tk_2539_, v___x_2523_);
v___x_3368_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3371_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3349_) == 1)
{
lean_object* v_val_3372_; lean_object* v___x_3373_; 
v_val_3372_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_val_3372_);
v___x_3373_ = l_Array_mkArray1___redArg(v_val_3372_);
v___y_3243_ = v___x_3366_;
v___y_3244_ = v___y_3357_;
v___y_3245_ = v___x_3370_;
v___y_3246_ = v___y_3345_;
v___y_3247_ = v___x_3371_;
v___y_3248_ = v___x_3364_;
v___y_3249_ = v___y_3346_;
v___y_3250_ = v___y_3347_;
v___y_3251_ = v___y_3356_;
v___y_3252_ = v___y_3352_;
v___y_3253_ = v___y_3348_;
v___y_3254_ = v___y_3351_;
v___y_3255_ = v___y_3344_;
v___y_3256_ = v___y_3358_;
v___y_3257_ = v___y_3354_;
v___y_3258_ = v___x_3369_;
v___y_3259_ = v___y_3355_;
v___y_3260_ = v___y_3353_;
v___y_3261_ = v_argsArray_3350_;
v___y_3262_ = v___y_3349_;
v___y_3263_ = v___x_3373_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3243_ = v___x_3366_;
v___y_3244_ = v___y_3357_;
v___y_3245_ = v___x_3370_;
v___y_3246_ = v___y_3345_;
v___y_3247_ = v___x_3371_;
v___y_3248_ = v___x_3364_;
v___y_3249_ = v___y_3346_;
v___y_3250_ = v___y_3347_;
v___y_3251_ = v___y_3356_;
v___y_3252_ = v___y_3352_;
v___y_3253_ = v___y_3348_;
v___y_3254_ = v___y_3351_;
v___y_3255_ = v___y_3344_;
v___y_3256_ = v___y_3358_;
v___y_3257_ = v___y_3354_;
v___y_3258_ = v___x_3369_;
v___y_3259_ = v___y_3355_;
v___y_3260_ = v___y_3353_;
v___y_3261_ = v_argsArray_3350_;
v___y_3262_ = v___y_3349_;
v___y_3263_ = v___x_3374_;
goto v___jp_3242_;
}
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3386_, v___y_3387_, v___y_3383_, v___y_3389_, v___y_3384_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = l_Lean_LibrarySuggestions_select(v_a_3393_, v___y_3391_, v___y_3387_, v___y_3383_, v___y_3389_, v___y_3384_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; size_t v_sz_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v_sz_3396_ = lean_array_size(v_a_3395_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3395_, v_sz_3396_, v___x_3397_, v___y_3376_, v___y_3377_, v___y_3386_, v___y_3388_, v___y_3382_, v___y_3387_, v___y_3383_, v___y_3389_, v___y_3384_);
lean_dec(v_a_3395_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___y_3344_ = v___y_3385_;
v___y_3345_ = v___y_3378_;
v___y_3346_ = v___y_3380_;
v___y_3347_ = v___y_3379_;
v___y_3348_ = v___y_3381_;
v___y_3349_ = v___y_3390_;
v_argsArray_3350_ = v_a_3399_;
v___y_3351_ = v___y_3377_;
v___y_3352_ = v___y_3386_;
v___y_3353_ = v___y_3388_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___y_3387_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3389_;
v___y_3358_ = v___y_3384_;
goto v___jp_3343_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v___y_3390_);
lean_dec(v___y_3385_);
lean_dec(v___y_3381_);
lean_dec(v___y_3379_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v_a_3400_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3398_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___y_3390_);
lean_dec(v___y_3385_);
lean_dec(v___y_3381_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3376_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v_a_3408_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3394_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3394_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v___y_3385_);
lean_dec(v___y_3381_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3376_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v_a_3416_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3392_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3392_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
v___jp_3424_:
{
lean_object* v_config_3441_; uint8_t v_suggestions_3442_; 
v_config_3441_ = lean_ctor_get(v___y_3426_, 0);
lean_inc_ref(v_config_3441_);
lean_dec_ref(v___y_3426_);
v_suggestions_3442_ = lean_ctor_get_uint8(v_config_3441_, sizeof(void*)*3 + 26);
if (v_suggestions_3442_ == 0)
{
lean_dec_ref(v_config_3441_);
lean_dec_ref(v___f_2527_);
v___y_3344_ = v___y_3434_;
v___y_3345_ = v___y_3427_;
v___y_3346_ = v___y_3429_;
v___y_3347_ = v___y_3428_;
v___y_3348_ = v___y_3430_;
v___y_3349_ = v___y_3439_;
v_argsArray_3350_ = v___y_3440_;
v___y_3351_ = v___y_3425_;
v___y_3352_ = v___y_3435_;
v___y_3353_ = v___y_3437_;
v___y_3354_ = v___y_3431_;
v___y_3355_ = v___y_3436_;
v___y_3356_ = v___y_3432_;
v___y_3357_ = v___y_3438_;
v___y_3358_ = v___y_3433_;
goto v___jp_3343_;
}
else
{
lean_object* v_maxSuggestions_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_maxSuggestions_3443_ = lean_ctor_get(v_config_3441_, 2);
lean_inc(v_maxSuggestions_3443_);
lean_dec_ref(v_config_3441_);
v___x_3444_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3445_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3443_) == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(100u);
v___x_3447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_3444_);
lean_ctor_set(v___x_3447_, 2, v___f_2527_);
lean_ctor_set(v___x_3447_, 3, v___x_3445_);
v___y_3376_ = v___y_3440_;
v___y_3377_ = v___y_3425_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___y_3428_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3431_;
v___y_3383_ = v___y_3432_;
v___y_3384_ = v___y_3433_;
v___y_3385_ = v___y_3434_;
v___y_3386_ = v___y_3435_;
v___y_3387_ = v___y_3436_;
v___y_3388_ = v___y_3437_;
v___y_3389_ = v___y_3438_;
v___y_3390_ = v___y_3439_;
v___y_3391_ = v___x_3447_;
goto v___jp_3375_;
}
else
{
lean_object* v_val_3448_; lean_object* v___x_3449_; 
v_val_3448_ = lean_ctor_get(v_maxSuggestions_3443_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v_maxSuggestions_3443_, 1);
v___x_3449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3449_, 0, v_val_3448_);
lean_ctor_set(v___x_3449_, 1, v___x_3444_);
lean_ctor_set(v___x_3449_, 2, v___f_2527_);
lean_ctor_set(v___x_3449_, 3, v___x_3445_);
v___y_3376_ = v___y_3440_;
v___y_3377_ = v___y_3425_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___y_3428_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3431_;
v___y_3383_ = v___y_3432_;
v___y_3384_ = v___y_3433_;
v___y_3385_ = v___y_3434_;
v___y_3386_ = v___y_3435_;
v___y_3387_ = v___y_3436_;
v___y_3388_ = v___y_3437_;
v___y_3389_ = v___y_3438_;
v___y_3390_ = v___y_3439_;
v___y_3391_ = v___x_3449_;
goto v___jp_3375_;
}
}
}
v___jp_3450_:
{
uint8_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = 1;
lean_inc(v___y_3458_);
v___x_3466_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3458_, v___x_3465_, v___y_3451_, v___y_3463_, v___y_3459_);
if (lean_obj_tag(v___x_3466_) == 0)
{
if (lean_obj_tag(v___y_3456_) == 1)
{
lean_object* v_a_3467_; lean_object* v_val_3468_; lean_object* v___x_3469_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v_val_3468_ = lean_ctor_get(v___y_3456_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___y_3456_, 1);
v___x_3469_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3468_);
lean_dec(v_val_3468_);
v___y_3425_ = v___y_3451_;
v___y_3426_ = v_a_3467_;
v___y_3427_ = v___x_3465_;
v___y_3428_ = v___y_3453_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3454_;
v___y_3431_ = v___y_3455_;
v___y_3432_ = v___y_3457_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3458_;
v___y_3435_ = v___y_3460_;
v___y_3436_ = v___y_3461_;
v___y_3437_ = v___y_3462_;
v___y_3438_ = v___y_3463_;
v___y_3439_ = v___y_3464_;
v___y_3440_ = v___x_3469_;
goto v___jp_3424_;
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
lean_dec(v___y_3456_);
v_a_3470_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3471_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3425_ = v___y_3451_;
v___y_3426_ = v_a_3470_;
v___y_3427_ = v___x_3465_;
v___y_3428_ = v___y_3453_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3454_;
v___y_3431_ = v___y_3455_;
v___y_3432_ = v___y_3457_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3458_;
v___y_3435_ = v___y_3460_;
v___y_3436_ = v___y_3461_;
v___y_3437_ = v___y_3462_;
v___y_3438_ = v___y_3463_;
v___y_3439_ = v___y_3464_;
v___y_3440_ = v___x_3471_;
goto v___jp_3424_;
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v___y_3464_);
lean_dec(v___y_3458_);
lean_dec(v___y_3456_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v_a_3472_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3466_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3466_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
v___jp_3480_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Syntax_getOptional_x3f(v___y_3485_);
lean_dec(v___y_3485_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_box(0);
v___y_3451_ = v___y_3487_;
v___y_3452_ = v___y_3483_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3484_;
v___y_3455_ = v___y_3490_;
v___y_3456_ = v_args_3486_;
v___y_3457_ = v___y_3492_;
v___y_3458_ = v___y_3481_;
v___y_3459_ = v___y_3494_;
v___y_3460_ = v___y_3488_;
v___y_3461_ = v___y_3491_;
v___y_3462_ = v___y_3489_;
v___y_3463_ = v___y_3493_;
v___y_3464_ = v___x_3496_;
goto v___jp_3450_;
}
else
{
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_val_3497_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3495_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v___x_3495_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_val_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
v___y_3451_ = v___y_3487_;
v___y_3452_ = v___y_3483_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3484_;
v___y_3455_ = v___y_3490_;
v___y_3456_ = v_args_3486_;
v___y_3457_ = v___y_3492_;
v___y_3458_ = v___y_3481_;
v___y_3459_ = v___y_3494_;
v___y_3460_ = v___y_3488_;
v___y_3461_ = v___y_3491_;
v___y_3462_ = v___y_3489_;
v___y_3463_ = v___y_3493_;
v___y_3464_ = v___x_3502_;
goto v___jp_3450_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v___x_3521_ = lean_unsigned_to_nat(3u);
v___x_3522_ = l_Lean_Syntax_getArg(v___y_3507_, v___x_3521_);
lean_dec(v___y_3507_);
v___x_3523_ = l_Lean_Syntax_isNone(v___x_3522_);
if (v___x_3523_ == 0)
{
uint8_t v___x_3524_; 
lean_inc(v___x_3522_);
v___x_3524_ = l_Lean_Syntax_matchesNull(v___x_3522_, v___x_3505_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
lean_dec(v___x_3522_);
lean_dec(v_o_3512_);
lean_dec(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3525_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3525_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3526_ = l_Lean_Syntax_getArg(v___x_3522_, v___x_2538_);
lean_dec(v___x_3522_);
v___x_3527_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3528_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3527_);
lean_inc(v___x_3526_);
v___x_3529_ = l_Lean_Syntax_isOfKind(v___x_3526_, v___x_3528_);
lean_dec(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec(v___x_3526_);
lean_dec(v_o_3512_);
lean_dec(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v_args_3532_; lean_object* v___x_3533_; 
v___x_3531_ = l_Lean_Syntax_getArg(v___x_3526_, v___x_3505_);
lean_dec(v___x_3526_);
v_args_3532_ = l_Lean_Syntax_getArgs(v___x_3531_);
lean_dec(v___x_3531_);
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v_args_3532_);
v___y_3481_ = v___y_3508_;
v___y_3482_ = v___y_3510_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v_o_3512_;
v___y_3485_ = v___y_3511_;
v_args_3486_ = v___x_3533_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
v___y_3494_ = v___y_3520_;
goto v___jp_3480_;
}
}
}
else
{
lean_object* v___x_3534_; 
lean_dec(v___x_3522_);
v___x_3534_ = lean_box(0);
v___y_3481_ = v___y_3508_;
v___y_3482_ = v___y_3510_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v_o_3512_;
v___y_3485_ = v___y_3511_;
v_args_3486_ = v___x_3534_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
v___y_3494_ = v___y_3520_;
goto v___jp_3480_;
}
}
v___jp_3535_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3545_ = lean_unsigned_to_nat(2u);
v___x_3546_ = l_Lean_Syntax_getArg(v_stx_2522_, v___x_3545_);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3548_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3547_);
lean_inc(v___x_3546_);
v___x_3549_ = l_Lean_Syntax_isOfKind(v___x_3546_, v___x_3548_);
lean_dec(v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
lean_dec(v___x_3546_);
lean_dec(v_bang_3536_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3550_;
}
else
{
lean_object* v_cfg_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_cfg_3551_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_2538_);
v___x_3552_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
lean_inc_ref(v___x_2524_);
v___x_3553_ = l_Lean_Name_mkStr4(v___x_2524_, v___x_2525_, v___x_2526_, v___x_3552_);
lean_inc(v_cfg_3551_);
v___x_3554_ = l_Lean_Syntax_isOfKind(v_cfg_3551_, v___x_3553_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec(v_cfg_3551_);
lean_dec(v___x_3546_);
lean_dec(v_bang_3536_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_3505_);
v___x_3557_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_3545_);
v___x_3558_ = l_Lean_Syntax_isNone(v___x_3557_);
if (v___x_3558_ == 0)
{
uint8_t v___x_3559_; 
lean_inc(v___x_3557_);
v___x_3559_ = l_Lean_Syntax_matchesNull(v___x_3557_, v___x_3505_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
lean_dec(v___x_3557_);
lean_dec(v___x_3556_);
lean_dec(v_cfg_3551_);
lean_dec(v___x_3546_);
lean_dec(v_bang_3536_);
lean_dec(v_tk_2539_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2524_);
v___x_3560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3560_;
}
else
{
lean_object* v_o_3561_; lean_object* v___x_3562_; 
v_o_3561_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_2538_);
lean_dec(v___x_3557_);
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_o_3561_);
v___y_3507_ = v___x_3546_;
v___y_3508_ = v_cfg_3551_;
v___y_3509_ = v___x_3554_;
v___y_3510_ = v_bang_3536_;
v___y_3511_ = v___x_3556_;
v_o_3512_ = v___x_3562_;
v___y_3513_ = v___y_3537_;
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___y_3539_;
v___y_3516_ = v___y_3540_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3542_;
v___y_3519_ = v___y_3543_;
v___y_3520_ = v___y_3544_;
goto v___jp_3506_;
}
}
else
{
lean_object* v___x_3563_; 
lean_dec(v___x_3557_);
v___x_3563_ = lean_box(0);
v___y_3507_ = v___x_3546_;
v___y_3508_ = v_cfg_3551_;
v___y_3509_ = v___x_3554_;
v___y_3510_ = v_bang_3536_;
v___y_3511_ = v___x_3556_;
v_o_3512_ = v___x_3563_;
v___y_3513_ = v___y_3537_;
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___y_3539_;
v___y_3516_ = v___y_3540_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3542_;
v___y_3519_ = v___y_3543_;
v___y_3520_ = v___y_3544_;
goto v___jp_3506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3571_, lean_object* v_stx_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v___x_3575_, lean_object* v___x_3576_, lean_object* v___f_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
uint8_t v___x_39049__boxed_3587_; uint8_t v___x_39050__boxed_3588_; lean_object* v_res_3589_; 
v___x_39049__boxed_3587_ = lean_unbox(v___x_3571_);
v___x_39050__boxed_3588_ = lean_unbox(v___x_3573_);
v_res_3589_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39049__boxed_3587_, v_stx_3572_, v___x_39050__boxed_3588_, v___x_3574_, v___x_3575_, v___x_3576_, v___f_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v_stx_3572_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; uint8_t v___x_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___y_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3609_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3596_);
v___x_3610_ = l_Lean_Syntax_isOfKind(v_stx_3596_, v___x_3609_);
v___x_3611_ = 1;
v___f_3612_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3613_ = lean_box(v___x_3610_);
v___x_3614_ = lean_box(v___x_3611_);
v___y_3615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3615_, 0, v___x_3613_);
lean_closure_set(v___y_3615_, 1, v_stx_3596_);
lean_closure_set(v___y_3615_, 2, v___x_3614_);
lean_closure_set(v___y_3615_, 3, v___x_3606_);
lean_closure_set(v___y_3615_, 4, v___x_3607_);
lean_closure_set(v___y_3615_, 5, v___x_3608_);
lean_closure_set(v___y_3615_, 6, v___f_3612_);
v___x_3616_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3616_, 0, v___y_3615_);
v___x_3617_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3616_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3629_, lean_object* v_as_3630_, lean_object* v_as_x27_3631_, lean_object* v_b_3632_, lean_object* v_a_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3629_, v_as_x27_3631_, v_b_3632_, v___y_3640_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3644_, lean_object* v_as_3645_, lean_object* v_as_x27_3646_, lean_object* v_b_3647_, lean_object* v_a_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3644_, v_as_3645_, v_as_x27_3646_, v_b_3647_, v_a_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v_as_x27_3646_);
lean_dec(v_as_3645_);
lean_dec(v___x_3644_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3666_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3668_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3669_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3670_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3666_, v___x_3667_, v___x_3668_, v___x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3700_ = l_Lean_addBuiltinDeclarationRanges(v___x_3698_, v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3703_, lean_object* v_simprocs_3704_, lean_object* v_fvarIdsToSimp_3705_, uint8_t v_simplifyTarget_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = lean_unsigned_to_nat(32u);
v___x_3716_ = lean_mk_empty_array_with_capacity(v___x_3715_);
lean_dec_ref(v___x_3716_);
v___x_3717_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3718_ = l_Lean_Meta_dsimpGoal(v_a_3714_, v_ctx_3703_, v_simprocs_3704_, v_simplifyTarget_3706_, v_fvarIdsToSimp_3705_, v___x_3717_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v_fst_3720_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v_fst_3720_ = lean_ctor_get(v_a_3719_, 0);
if (lean_obj_tag(v_fst_3720_) == 0)
{
lean_object* v_snd_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_snd_3721_ = lean_ctor_get(v_a_3719_, 1);
lean_inc(v_snd_3721_);
lean_dec(v_a_3719_);
v___x_3722_ = lean_box(0);
v___x_3723_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3722_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v___x_3723_, 0);
lean_dec(v_unused_3731_);
v___x_3725_ = v___x_3723_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v___x_3723_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v_snd_3721_);
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_snd_3721_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_snd_3721_);
v_a_3732_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3723_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3723_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_snd_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3766_; 
lean_inc_ref(v_fst_3720_);
v_snd_3740_ = lean_ctor_get(v_a_3719_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_a_3719_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; 
v_unused_3767_ = lean_ctor_get(v_a_3719_, 0);
lean_dec(v_unused_3767_);
v___x_3742_ = v_a_3719_;
v_isShared_3743_ = v_isSharedCheck_3766_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_snd_3740_);
lean_dec(v_a_3719_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3766_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v_val_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v_val_3744_ = lean_ctor_get(v_fst_3720_, 0);
lean_inc(v_val_3744_);
lean_dec_ref_known(v_fst_3720_, 1);
v___x_3745_ = lean_box(0);
if (v_isShared_3743_ == 0)
{
lean_ctor_set_tag(v___x_3742_, 1);
lean_ctor_set(v___x_3742_, 1, v___x_3745_);
lean_ctor_set(v___x_3742_, 0, v_val_3744_);
v___x_3747_ = v___x_3742_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_val_3744_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3747_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3756_);
v___x_3750_ = v___x_3748_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v___x_3748_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_snd_3740_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_snd_3740_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_snd_3740_);
v_a_3757_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3748_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3748_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v_a_3768_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3718_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3718_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec_ref(v_fvarIdsToSimp_3705_);
lean_dec_ref(v_simprocs_3704_);
lean_dec_ref(v_ctx_3703_);
v_a_3776_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3713_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3713_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3784_, lean_object* v_simprocs_3785_, lean_object* v_fvarIdsToSimp_3786_, lean_object* v_simplifyTarget_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
uint8_t v_simplifyTarget_boxed_3794_; lean_object* v_res_3795_; 
v_simplifyTarget_boxed_3794_ = lean_unbox(v_simplifyTarget_3787_);
v_res_3795_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3784_, v_simprocs_3785_, v_fvarIdsToSimp_3786_, v_simplifyTarget_boxed_3794_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3796_, lean_object* v_simprocs_3797_, lean_object* v_fvarIdsToSimp_3798_, uint8_t v_simplifyTarget_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3796_, v_simprocs_3797_, v_fvarIdsToSimp_3798_, v_simplifyTarget_3799_, v_a_3801_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3810_, lean_object* v_simprocs_3811_, lean_object* v_fvarIdsToSimp_3812_, lean_object* v_simplifyTarget_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
uint8_t v_simplifyTarget_boxed_3823_; lean_object* v_res_3824_; 
v_simplifyTarget_boxed_3823_ = lean_unbox(v_simplifyTarget_3813_);
v_res_3824_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3810_, v_simprocs_3811_, v_fvarIdsToSimp_3812_, v_simplifyTarget_boxed_3823_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3825_, lean_object* v_simprocs_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3828_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v___x_3838_ = l_Lean_MVarId_getNondepPropHyps(v_a_3837_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; uint8_t v___x_3840_; lean_object* v___x_3841_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = 1;
v___x_3841_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3825_, v_simprocs_3826_, v_a_3839_, v___x_3840_, v___y_3828_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3841_;
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v_simprocs_3826_);
lean_dec_ref(v_ctx_3825_);
v_a_3842_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3838_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3838_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_simprocs_3826_);
lean_dec_ref(v_ctx_3825_);
v_a_3850_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3836_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3836_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3858_, lean_object* v_simprocs_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3858_, v_simprocs_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3870_, lean_object* v_ctx_3871_, lean_object* v_simprocs_3872_, uint8_t v_type_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3870_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3871_, v_simprocs_3872_, v_a_3884_, v_type_3873_, v___y_3875_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3885_;
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v_simprocs_3872_);
lean_dec_ref(v_ctx_3871_);
v_a_3886_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3883_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3883_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3894_, lean_object* v_ctx_3895_, lean_object* v_simprocs_3896_, lean_object* v_type_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
uint8_t v_type_633__boxed_3907_; lean_object* v_res_3908_; 
v_type_633__boxed_3907_ = lean_unbox(v_type_3897_);
v_res_3908_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3894_, v_ctx_3895_, v_simprocs_3896_, v_type_633__boxed_3907_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3909_, lean_object* v_simprocs_3910_, lean_object* v_loc_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
if (lean_obj_tag(v_loc_3911_) == 0)
{
lean_object* v___f_3921_; lean_object* v___x_3922_; 
v___f_3921_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3921_, 0, v_ctx_3909_);
lean_closure_set(v___f_3921_, 1, v_simprocs_3910_);
v___x_3922_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3921_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3922_;
}
else
{
lean_object* v_hypotheses_3923_; uint8_t v_type_3924_; lean_object* v___x_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; 
v_hypotheses_3923_ = lean_ctor_get(v_loc_3911_, 0);
lean_inc_ref(v_hypotheses_3923_);
v_type_3924_ = lean_ctor_get_uint8(v_loc_3911_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3911_, 1);
v___x_3925_ = lean_box(v_type_3924_);
v___f_3926_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3926_, 0, v_hypotheses_3923_);
lean_closure_set(v___f_3926_, 1, v_ctx_3909_);
lean_closure_set(v___f_3926_, 2, v_simprocs_3910_);
lean_closure_set(v___f_3926_, 3, v___x_3925_);
v___x_3927_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3926_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3928_, lean_object* v_simprocs_3929_, lean_object* v_loc_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3928_, v_simprocs_3929_, v_loc_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3945_, lean_object* v_stx_3946_, uint8_t v___x_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v___x_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
if (v___x_3945_ == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_3960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v_tk_3962_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4048_; lean_object* v___y_4049_; uint8_t v___y_4050_; lean_object* v_stx_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; uint8_t v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; uint8_t v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; uint8_t v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; uint8_t v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; uint8_t v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; uint8_t v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4317_; uint8_t v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v_args_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___x_4343_; lean_object* v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v_o_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v_bang_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v___x_3961_ = lean_unsigned_to_nat(0u);
v_tk_3962_ = l_Lean_Syntax_getArg(v_stx_3946_, v___x_3961_);
v___x_4343_ = lean_unsigned_to_nat(1u);
v___x_4400_ = l_Lean_Syntax_getArg(v_stx_3946_, v___x_4343_);
v___x_4401_ = l_Lean_Syntax_isNone(v___x_4400_);
if (v___x_4401_ == 0)
{
uint8_t v___x_4402_; 
lean_inc(v___x_4400_);
v___x_4402_ = l_Lean_Syntax_matchesNull(v___x_4400_, v___x_4343_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; 
lean_dec(v___x_4400_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4403_;
}
else
{
lean_object* v_bang_4404_; lean_object* v___x_4405_; 
v_bang_4404_ = l_Lean_Syntax_getArg(v___x_4400_, v___x_3961_);
lean_dec(v___x_4400_);
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v_bang_4404_);
v_bang_4373_ = v___x_4405_;
v___y_4374_ = v___y_3951_;
v___y_4375_ = v___y_3952_;
v___y_4376_ = v___y_3953_;
v___y_4377_ = v___y_3954_;
v___y_4378_ = v___y_3955_;
v___y_4379_ = v___y_3956_;
v___y_4380_ = v___y_3957_;
v___y_4381_ = v___y_3958_;
goto v___jp_4372_;
}
}
else
{
lean_object* v___x_4406_; 
lean_dec(v___x_4400_);
v___x_4406_ = lean_box(0);
v_bang_4373_ = v___x_4406_;
v___y_4374_ = v___y_3951_;
v___y_4375_ = v___y_3952_;
v___y_4376_ = v___y_3953_;
v___y_4377_ = v___y_3954_;
v___y_4378_ = v___y_3955_;
v___y_4379_ = v___y_3956_;
v___y_4380_ = v___y_3957_;
v___y_4381_ = v___y_3958_;
goto v___jp_4372_;
}
v___jp_3963_:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3971_, v___y_3964_, v___y_3975_, v___y_3974_, v___y_3969_, v___y_3968_, v___y_3970_, v___y_3966_, v___y_3973_, v___y_3972_, v___y_3967_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v_usedTheorems_3978_; lean_object* v_diag_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4021_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v_usedTheorems_3978_ = lean_ctor_get(v_a_3977_, 0);
v_diag_3979_ = lean_ctor_get(v_a_3977_, 1);
v_isSharedCheck_4021_ = !lean_is_exclusive(v_a_3977_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3981_ = v_a_3977_;
v_isShared_3982_ = v_isSharedCheck_4021_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_diag_3979_);
lean_inc(v_usedTheorems_3978_);
lean_dec(v_a_3977_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4021_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3965_, v_usedTheorems_3978_, v___y_3966_, v___y_3973_, v___y_3972_, v___y_3967_);
lean_dec_ref(v_usedTheorems_3978_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v_ref_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v_ref_3985_ = lean_ctor_get(v___y_3972_, 5);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 1, v_a_3984_);
lean_ctor_set(v___x_3981_, 0, v___x_3986_);
v___x_3988_ = v___x_3981_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_a_3984_);
v___x_3988_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3989_ = lean_box(0);
v___x_3990_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
lean_ctor_set(v___x_3990_, 2, v___x_3989_);
lean_ctor_set(v___x_3990_, 3, v___x_3989_);
lean_ctor_set(v___x_3990_, 4, v___x_3989_);
lean_ctor_set(v___x_3990_, 5, v___x_3989_);
lean_inc(v_ref_3985_);
v___x_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3991_, 0, v_ref_3985_);
v___x_3992_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3993_ = 4;
v___x_3994_ = l_Lean_MessageData_nil;
v___x_3995_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3962_, v___x_3990_, v___x_3991_, v___x_3992_, v___x_3989_, v___x_3993_, v___x_3994_, v___y_3972_, v___y_3967_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v___x_3995_, 0);
lean_dec(v_unused_4003_);
v___x_3997_ = v___x_3995_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_dec(v___x_3995_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v_diag_3979_);
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_diag_3979_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v_diag_3979_);
v_a_4004_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3995_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3995_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_del_object(v___x_3981_);
lean_dec_ref(v_diag_3979_);
lean_dec(v_tk_3962_);
v_a_4013_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3983_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3983_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v___y_3965_);
lean_dec(v_tk_3962_);
v_a_4022_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3976_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3976_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
v___jp_4030_:
{
if (lean_obj_tag(v___y_4032_) == 0)
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4044_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*1, v___x_3947_);
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4033_;
v___y_3966_ = v___y_4034_;
v___y_3967_ = v___y_4035_;
v___y_3968_ = v___y_4037_;
v___y_3969_ = v___y_4036_;
v___y_3970_ = v___y_4038_;
v___y_3971_ = v___y_4042_;
v___y_3972_ = v___y_4041_;
v___y_3973_ = v___y_4040_;
v___y_3974_ = v___y_4039_;
v___y_3975_ = v___x_4044_;
goto v___jp_3963_;
}
else
{
lean_object* v_val_4045_; lean_object* v___x_4046_; 
v_val_4045_ = lean_ctor_get(v___y_4032_, 0);
lean_inc(v_val_4045_);
lean_dec_ref_known(v___y_4032_, 1);
v___x_4046_ = l_Lean_Elab_Tactic_expandLocation(v_val_4045_);
lean_dec(v_val_4045_);
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4033_;
v___y_3966_ = v___y_4034_;
v___y_3967_ = v___y_4035_;
v___y_3968_ = v___y_4037_;
v___y_3969_ = v___y_4036_;
v___y_3970_ = v___y_4038_;
v___y_3971_ = v___y_4042_;
v___y_3972_ = v___y_4041_;
v___y_3973_ = v___y_4040_;
v___y_3974_ = v___y_4039_;
v___y_3975_ = v___x_4046_;
goto v___jp_3963_;
}
}
v___jp_4047_:
{
uint8_t v___x_4060_; uint8_t v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4060_ = 0;
v___x_4061_ = 2;
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4063_ = lean_box(v___x_4060_);
v___x_4064_ = lean_box(v___x_4061_);
v___x_4065_ = lean_box(v___x_4060_);
lean_inc(v_stx_4051_);
v___x_4066_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4066_, 0, v_stx_4051_);
lean_closure_set(v___x_4066_, 1, v___x_4063_);
lean_closure_set(v___x_4066_, 2, v___x_4064_);
lean_closure_set(v___x_4066_, 3, v___x_4065_);
lean_closure_set(v___x_4066_, 4, v___x_4062_);
v___x_4067_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4066_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
if (lean_obj_tag(v___y_4048_) == 0)
{
lean_object* v_ctx_4069_; lean_object* v_simprocs_4070_; 
v_ctx_4069_ = lean_ctor_get(v_a_4068_, 0);
lean_inc_ref(v_ctx_4069_);
v_simprocs_4070_ = lean_ctor_get(v_a_4068_, 1);
lean_inc_ref(v_simprocs_4070_);
lean_dec(v_a_4068_);
v___y_4031_ = v_simprocs_4070_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v_stx_4051_;
v___y_4034_ = v___y_4056_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4053_;
v___y_4037_ = v___y_4054_;
v___y_4038_ = v___y_4055_;
v___y_4039_ = v___y_4052_;
v___y_4040_ = v___y_4057_;
v___y_4041_ = v___y_4058_;
v___y_4042_ = v_ctx_4069_;
goto v___jp_4030_;
}
else
{
lean_dec_ref_known(v___y_4048_, 1);
if (v___y_4050_ == 0)
{
lean_object* v_ctx_4071_; lean_object* v_simprocs_4072_; 
v_ctx_4071_ = lean_ctor_get(v_a_4068_, 0);
lean_inc_ref(v_ctx_4071_);
v_simprocs_4072_ = lean_ctor_get(v_a_4068_, 1);
lean_inc_ref(v_simprocs_4072_);
lean_dec(v_a_4068_);
v___y_4031_ = v_simprocs_4072_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v_stx_4051_;
v___y_4034_ = v___y_4056_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4053_;
v___y_4037_ = v___y_4054_;
v___y_4038_ = v___y_4055_;
v___y_4039_ = v___y_4052_;
v___y_4040_ = v___y_4057_;
v___y_4041_ = v___y_4058_;
v___y_4042_ = v_ctx_4071_;
goto v___jp_4030_;
}
else
{
lean_object* v_ctx_4073_; lean_object* v_simprocs_4074_; lean_object* v___x_4075_; 
v_ctx_4073_ = lean_ctor_get(v_a_4068_, 0);
lean_inc_ref(v_ctx_4073_);
v_simprocs_4074_ = lean_ctor_get(v_a_4068_, 1);
lean_inc_ref(v_simprocs_4074_);
lean_dec(v_a_4068_);
v___x_4075_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4073_);
v___y_4031_ = v_simprocs_4074_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v_stx_4051_;
v___y_4034_ = v___y_4056_;
v___y_4035_ = v___y_4059_;
v___y_4036_ = v___y_4053_;
v___y_4037_ = v___y_4054_;
v___y_4038_ = v___y_4055_;
v___y_4039_ = v___y_4052_;
v___y_4040_ = v___y_4057_;
v___y_4041_ = v___y_4058_;
v___y_4042_ = v___x_4075_;
goto v___jp_4030_;
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_stx_4051_);
lean_dec(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v_tk_3962_);
v_a_4076_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4067_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4067_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
v___jp_4084_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_inc_ref(v___y_4086_);
v___x_4106_ = l_Array_append___redArg(v___y_4086_, v___y_4105_);
lean_dec_ref(v___y_4105_);
lean_inc(v___y_4100_);
lean_inc(v___y_4103_);
v___x_4107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4107_, 0, v___y_4103_);
lean_ctor_set(v___x_4107_, 1, v___y_4100_);
lean_ctor_set(v___x_4107_, 2, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_node6(v___y_4103_, v___y_4088_, v___y_4097_, v___y_4101_, v___y_4104_, v___y_4085_, v___y_4094_, v___x_4107_);
v___y_4048_ = v___y_4092_;
v___y_4049_ = v___y_4093_;
v___y_4050_ = v___y_4098_;
v_stx_4051_ = v___x_4108_;
v___y_4052_ = v___y_4087_;
v___y_4053_ = v___y_4089_;
v___y_4054_ = v___y_4099_;
v___y_4055_ = v___y_4095_;
v___y_4056_ = v___y_4090_;
v___y_4057_ = v___y_4091_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4102_;
goto v___jp_4047_;
}
v___jp_4109_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_inc_ref(v___y_4111_);
v___x_4130_ = l_Array_append___redArg(v___y_4111_, v___y_4129_);
lean_dec_ref(v___y_4129_);
lean_inc(v___y_4124_);
lean_inc(v___y_4127_);
v___x_4131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4131_, 0, v___y_4127_);
lean_ctor_set(v___x_4131_, 1, v___y_4124_);
lean_ctor_set(v___x_4131_, 2, v___x_4130_);
if (lean_obj_tag(v___y_4118_) == 0)
{
lean_object* v___x_4132_; 
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4111_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4113_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4115_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4118_;
v___y_4094_ = v___x_4131_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4121_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___y_4122_;
v___y_4099_ = v___y_4123_;
v___y_4100_ = v___y_4124_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___y_4127_;
v___y_4104_ = v___y_4128_;
v___y_4105_ = v___x_4132_;
goto v___jp_4084_;
}
else
{
lean_object* v_val_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_val_4133_ = lean_ctor_get(v___y_4118_, 0);
v___x_4134_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4133_);
v___x_4135_ = lean_array_push(v___x_4134_, v_val_4133_);
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4111_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4113_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4115_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4118_;
v___y_4094_ = v___x_4131_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4121_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___y_4122_;
v___y_4099_ = v___y_4123_;
v___y_4100_ = v___y_4124_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___y_4127_;
v___y_4104_ = v___y_4128_;
v___y_4105_ = v___x_4135_;
goto v___jp_4084_;
}
}
v___jp_4136_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_inc_ref(v___y_4137_);
v___x_4157_ = l_Array_append___redArg(v___y_4137_, v___y_4156_);
lean_dec_ref(v___y_4156_);
lean_inc(v___y_4151_);
lean_inc(v___y_4154_);
v___x_4158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4158_, 0, v___y_4154_);
lean_ctor_set(v___x_4158_, 1, v___y_4151_);
lean_ctor_set(v___x_4158_, 2, v___x_4157_);
if (lean_obj_tag(v___y_4143_) == 1)
{
lean_object* v_val_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_val_4159_ = lean_ctor_get(v___y_4143_, 0);
lean_inc(v_val_4159_);
lean_dec_ref_known(v___y_4143_, 1);
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4154_, 3);
v___x_4161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___y_4154_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
lean_inc_ref(v___y_4137_);
v___x_4162_ = l_Array_append___redArg(v___y_4137_, v_val_4159_);
lean_dec(v_val_4159_);
lean_inc(v___y_4151_);
v___x_4163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4163_, 0, v___y_4154_);
lean_ctor_set(v___x_4163_, 1, v___y_4151_);
lean_ctor_set(v___x_4163_, 2, v___x_4162_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___y_4154_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Array_mkArray3___redArg(v___x_4161_, v___x_4163_, v___x_4165_);
v___y_4110_ = v___x_4158_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4138_;
v___y_4113_ = v___y_4139_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4141_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4144_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4148_;
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4151_;
v___y_4125_ = v___y_4152_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___y_4154_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___x_4166_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4167_; 
lean_dec(v___y_4143_);
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4110_ = v___x_4158_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4138_;
v___y_4113_ = v___y_4139_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4141_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4144_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4148_;
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4151_;
v___y_4125_ = v___y_4152_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___y_4154_;
v___y_4128_ = v___y_4155_;
v___y_4129_ = v___x_4167_;
goto v___jp_4109_;
}
}
v___jp_4168_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_inc_ref(v___y_4187_);
v___x_4190_ = l_Array_append___redArg(v___y_4187_, v___y_4189_);
lean_dec_ref(v___y_4189_);
lean_inc(v___y_4171_);
lean_inc(v___y_4182_);
v___x_4191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4191_, 0, v___y_4182_);
lean_ctor_set(v___x_4191_, 1, v___y_4171_);
lean_ctor_set(v___x_4191_, 2, v___x_4190_);
v___x_4192_ = l_Lean_Syntax_node6(v___y_4182_, v___y_4184_, v___y_4181_, v___y_4185_, v___y_4188_, v___y_4172_, v___y_4175_, v___x_4191_);
v___y_4048_ = v___y_4176_;
v___y_4049_ = v___y_4177_;
v___y_4050_ = v___y_4180_;
v_stx_4051_ = v___x_4192_;
v___y_4052_ = v___y_4169_;
v___y_4053_ = v___y_4170_;
v___y_4054_ = v___y_4183_;
v___y_4055_ = v___y_4178_;
v___y_4056_ = v___y_4173_;
v___y_4057_ = v___y_4174_;
v___y_4058_ = v___y_4179_;
v___y_4059_ = v___y_4186_;
goto v___jp_4047_;
}
v___jp_4193_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_inc_ref(v___y_4212_);
v___x_4214_ = l_Array_append___redArg(v___y_4212_, v___y_4213_);
lean_dec_ref(v___y_4213_);
lean_inc(v___y_4196_);
lean_inc(v___y_4207_);
v___x_4215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4215_, 0, v___y_4207_);
lean_ctor_set(v___x_4215_, 1, v___y_4196_);
lean_ctor_set(v___x_4215_, 2, v___x_4214_);
if (lean_obj_tag(v___y_4201_) == 0)
{
lean_object* v___x_4216_; 
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4199_;
v___y_4175_ = v___x_4215_;
v___y_4176_ = v___y_4200_;
v___y_4177_ = v___y_4201_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___y_4207_;
v___y_4183_ = v___y_4206_;
v___y_4184_ = v___y_4209_;
v___y_4185_ = v___y_4208_;
v___y_4186_ = v___y_4210_;
v___y_4187_ = v___y_4212_;
v___y_4188_ = v___y_4211_;
v___y_4189_ = v___x_4216_;
goto v___jp_4168_;
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_val_4217_ = lean_ctor_get(v___y_4201_, 0);
v___x_4218_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4217_);
v___x_4219_ = lean_array_push(v___x_4218_, v_val_4217_);
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4199_;
v___y_4175_ = v___x_4215_;
v___y_4176_ = v___y_4200_;
v___y_4177_ = v___y_4201_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___y_4207_;
v___y_4183_ = v___y_4206_;
v___y_4184_ = v___y_4209_;
v___y_4185_ = v___y_4208_;
v___y_4186_ = v___y_4210_;
v___y_4187_ = v___y_4212_;
v___y_4188_ = v___y_4211_;
v___y_4189_ = v___x_4219_;
goto v___jp_4168_;
}
}
v___jp_4220_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_inc_ref(v___y_4239_);
v___x_4241_ = l_Array_append___redArg(v___y_4239_, v___y_4240_);
lean_dec_ref(v___y_4240_);
lean_inc(v___y_4223_);
lean_inc(v___y_4234_);
v___x_4242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4242_, 0, v___y_4234_);
lean_ctor_set(v___x_4242_, 1, v___y_4223_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
if (lean_obj_tag(v___y_4226_) == 1)
{
lean_object* v_val_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v_val_4243_ = lean_ctor_get(v___y_4226_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v___y_4226_, 1);
v___x_4244_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4234_, 3);
v___x_4245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___y_4234_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
lean_inc_ref(v___y_4239_);
v___x_4246_ = l_Array_append___redArg(v___y_4239_, v_val_4243_);
lean_dec(v_val_4243_);
lean_inc(v___y_4223_);
v___x_4247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4247_, 0, v___y_4234_);
lean_ctor_set(v___x_4247_, 1, v___y_4223_);
lean_ctor_set(v___x_4247_, 2, v___x_4246_);
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___y_4234_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l_Array_mkArray3___redArg(v___x_4245_, v___x_4247_, v___x_4249_);
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___x_4242_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___y_4225_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4236_;
v___y_4209_ = v___y_4235_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___y_4238_;
v___y_4212_ = v___y_4239_;
v___y_4213_ = v___x_4250_;
goto v___jp_4193_;
}
else
{
lean_object* v___x_4251_; 
lean_dec(v___y_4226_);
v___x_4251_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___x_4242_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___y_4225_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4236_;
v___y_4209_ = v___y_4235_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___y_4238_;
v___y_4212_ = v___y_4239_;
v___y_4213_ = v___x_4251_;
goto v___jp_4193_;
}
}
v___jp_4252_:
{
lean_object* v_ref_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_ref_4268_ = lean_ctor_get(v___y_4262_, 5);
v___x_4269_ = l_Lean_SourceInfo_fromRef(v_ref_4268_, v___y_4267_);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4271_ = l_Lean_Name_mkStr4(v___x_3948_, v___x_3949_, v___x_3950_, v___x_4270_);
v___x_4272_ = l_Lean_SourceInfo_fromRef(v_tk_3962_, v___x_3947_);
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
lean_ctor_set(v___x_4273_, 1, v___x_4270_);
v___x_4274_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4275_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4269_);
v___x_4276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4269_);
lean_ctor_set(v___x_4276_, 1, v___x_4274_);
lean_ctor_set(v___x_4276_, 2, v___x_4275_);
if (lean_obj_tag(v___y_4256_) == 1)
{
lean_object* v_val_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_val_4277_ = lean_ctor_get(v___y_4256_, 0);
lean_inc(v_val_4277_);
lean_dec_ref_known(v___y_4256_, 1);
v___x_4278_ = l_Lean_SourceInfo_fromRef(v_val_4277_, v___x_3947_);
lean_dec(v_val_4277_);
v___x_4279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l_Array_mkArray1___redArg(v___x_4280_);
v___y_4137_ = v___x_4275_;
v___y_4138_ = v___y_4253_;
v___y_4139_ = v___x_4271_;
v___y_4140_ = v___y_4254_;
v___y_4141_ = v___y_4255_;
v___y_4142_ = v___y_4257_;
v___y_4143_ = v___y_4258_;
v___y_4144_ = v___y_4259_;
v___y_4145_ = v___y_4260_;
v___y_4146_ = v___y_4261_;
v___y_4147_ = v___x_4273_;
v___y_4148_ = v___y_4262_;
v___y_4149_ = v___y_4263_;
v___y_4150_ = v___y_4264_;
v___y_4151_ = v___x_4274_;
v___y_4152_ = v___y_4265_;
v___y_4153_ = v___y_4266_;
v___y_4154_ = v___x_4269_;
v___y_4155_ = v___x_4276_;
v___y_4156_ = v___x_4281_;
goto v___jp_4136_;
}
else
{
lean_object* v___x_4282_; 
lean_dec(v___y_4256_);
v___x_4282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4137_ = v___x_4275_;
v___y_4138_ = v___y_4253_;
v___y_4139_ = v___x_4271_;
v___y_4140_ = v___y_4254_;
v___y_4141_ = v___y_4255_;
v___y_4142_ = v___y_4257_;
v___y_4143_ = v___y_4258_;
v___y_4144_ = v___y_4259_;
v___y_4145_ = v___y_4260_;
v___y_4146_ = v___y_4261_;
v___y_4147_ = v___x_4273_;
v___y_4148_ = v___y_4262_;
v___y_4149_ = v___y_4263_;
v___y_4150_ = v___y_4264_;
v___y_4151_ = v___x_4274_;
v___y_4152_ = v___y_4265_;
v___y_4153_ = v___y_4266_;
v___y_4154_ = v___x_4269_;
v___y_4155_ = v___x_4276_;
v___y_4156_ = v___x_4282_;
goto v___jp_4136_;
}
}
v___jp_4283_:
{
if (lean_obj_tag(v___y_4290_) == 0)
{
uint8_t v___x_4298_; 
v___x_4298_ = 0;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4288_;
v___y_4258_ = v___y_4289_;
v___y_4259_ = v___y_4290_;
v___y_4260_ = v___y_4297_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4292_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___y_4295_;
v___y_4266_ = v___y_4296_;
v___y_4267_ = v___x_4298_;
goto v___jp_4252_;
}
else
{
if (v___y_4293_ == 0)
{
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4288_;
v___y_4258_ = v___y_4289_;
v___y_4259_ = v___y_4290_;
v___y_4260_ = v___y_4297_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4292_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___y_4295_;
v___y_4266_ = v___y_4296_;
v___y_4267_ = v___y_4293_;
goto v___jp_4252_;
}
else
{
lean_object* v_ref_4299_; uint8_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_ref_4299_ = lean_ctor_get(v___y_4292_, 5);
v___x_4300_ = 0;
v___x_4301_ = l_Lean_SourceInfo_fromRef(v_ref_4299_, v___x_4300_);
v___x_4302_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4303_ = l_Lean_Name_mkStr4(v___x_3948_, v___x_3949_, v___x_3950_, v___x_4302_);
v___x_4304_ = l_Lean_SourceInfo_fromRef(v_tk_3962_, v___x_3947_);
v___x_4305_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4308_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4301_);
v___x_4309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4301_);
lean_ctor_set(v___x_4309_, 1, v___x_4307_);
lean_ctor_set(v___x_4309_, 2, v___x_4308_);
if (lean_obj_tag(v___y_4287_) == 1)
{
lean_object* v_val_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_val_4310_ = lean_ctor_get(v___y_4287_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v___y_4287_, 1);
v___x_4311_ = l_Lean_SourceInfo_fromRef(v_val_4310_, v___x_3947_);
lean_dec(v_val_4310_);
v___x_4312_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = l_Array_mkArray1___redArg(v___x_4313_);
v___y_4221_ = v___y_4284_;
v___y_4222_ = v___y_4285_;
v___y_4223_ = v___x_4307_;
v___y_4224_ = v___y_4286_;
v___y_4225_ = v___y_4288_;
v___y_4226_ = v___y_4289_;
v___y_4227_ = v___y_4290_;
v___y_4228_ = v___y_4297_;
v___y_4229_ = v___y_4291_;
v___y_4230_ = v___y_4292_;
v___y_4231_ = v___y_4293_;
v___y_4232_ = v___x_4306_;
v___y_4233_ = v___y_4294_;
v___y_4234_ = v___x_4301_;
v___y_4235_ = v___x_4303_;
v___y_4236_ = v___y_4295_;
v___y_4237_ = v___y_4296_;
v___y_4238_ = v___x_4309_;
v___y_4239_ = v___x_4308_;
v___y_4240_ = v___x_4314_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4315_; 
lean_dec(v___y_4287_);
v___x_4315_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4221_ = v___y_4284_;
v___y_4222_ = v___y_4285_;
v___y_4223_ = v___x_4307_;
v___y_4224_ = v___y_4286_;
v___y_4225_ = v___y_4288_;
v___y_4226_ = v___y_4289_;
v___y_4227_ = v___y_4290_;
v___y_4228_ = v___y_4297_;
v___y_4229_ = v___y_4291_;
v___y_4230_ = v___y_4292_;
v___y_4231_ = v___y_4293_;
v___y_4232_ = v___x_4306_;
v___y_4233_ = v___y_4294_;
v___y_4234_ = v___x_4301_;
v___y_4235_ = v___x_4303_;
v___y_4236_ = v___y_4295_;
v___y_4237_ = v___y_4296_;
v___y_4238_ = v___x_4309_;
v___y_4239_ = v___x_4308_;
v___y_4240_ = v___x_4315_;
goto v___jp_4220_;
}
}
}
}
v___jp_4316_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4331_ = lean_unsigned_to_nat(3u);
v___x_4332_ = l_Lean_Syntax_getArg(v___y_4320_, v___x_4331_);
lean_dec(v___y_4320_);
v___x_4333_ = l_Lean_Syntax_getOptional_x3f(v___x_4332_);
lean_dec(v___x_4332_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_box(0);
v___y_4284_ = v___y_4323_;
v___y_4285_ = v___y_4324_;
v___y_4286_ = v___y_4327_;
v___y_4287_ = v___y_4319_;
v___y_4288_ = v___y_4328_;
v___y_4289_ = v_args_4322_;
v___y_4290_ = v___y_4317_;
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4329_;
v___y_4293_ = v___y_4318_;
v___y_4294_ = v___y_4325_;
v___y_4295_ = v___y_4321_;
v___y_4296_ = v___y_4330_;
v___y_4297_ = v___x_4334_;
goto v___jp_4283_;
}
else
{
lean_object* v_val_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
v_val_4335_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4333_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_val_4335_);
lean_dec(v___x_4333_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_val_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
v___y_4284_ = v___y_4323_;
v___y_4285_ = v___y_4324_;
v___y_4286_ = v___y_4327_;
v___y_4287_ = v___y_4319_;
v___y_4288_ = v___y_4328_;
v___y_4289_ = v_args_4322_;
v___y_4290_ = v___y_4317_;
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4329_;
v___y_4293_ = v___y_4318_;
v___y_4294_ = v___y_4325_;
v___y_4295_ = v___y_4321_;
v___y_4296_ = v___y_4330_;
v___y_4297_ = v___x_4340_;
goto v___jp_4283_;
}
}
}
}
v___jp_4344_:
{
lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4359_ = l_Lean_Syntax_getArg(v___y_4348_, v___y_4346_);
v___x_4360_ = l_Lean_Syntax_isNone(v___x_4359_);
if (v___x_4360_ == 0)
{
uint8_t v___x_4361_; 
lean_inc(v___x_4359_);
v___x_4361_ = l_Lean_Syntax_matchesNull(v___x_4359_, v___x_4343_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
lean_dec(v___x_4359_);
lean_dec(v_o_4350_);
lean_dec(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec(v___y_4345_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4362_;
}
else
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4363_ = l_Lean_Syntax_getArg(v___x_4359_, v___x_3961_);
lean_dec(v___x_4359_);
v___x_4364_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3950_);
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
v___x_4365_ = l_Lean_Name_mkStr4(v___x_3948_, v___x_3949_, v___x_3950_, v___x_4364_);
lean_inc(v___x_4363_);
v___x_4366_ = l_Lean_Syntax_isOfKind(v___x_4363_, v___x_4365_);
lean_dec(v___x_4365_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
lean_dec(v___x_4363_);
lean_dec(v_o_4350_);
lean_dec(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec(v___y_4345_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4367_;
}
else
{
lean_object* v___x_4368_; lean_object* v_args_4369_; lean_object* v___x_4370_; 
v___x_4368_ = l_Lean_Syntax_getArg(v___x_4363_, v___x_4343_);
lean_dec(v___x_4363_);
v_args_4369_ = l_Lean_Syntax_getArgs(v___x_4368_);
lean_dec(v___x_4368_);
v___x_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4370_, 0, v_args_4369_);
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4347_;
v___y_4319_ = v_o_4350_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v_args_4322_ = v___x_4370_;
v___y_4323_ = v___y_4351_;
v___y_4324_ = v___y_4352_;
v___y_4325_ = v___y_4353_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4356_;
v___y_4329_ = v___y_4357_;
v___y_4330_ = v___y_4358_;
goto v___jp_4316_;
}
}
}
else
{
lean_object* v___x_4371_; 
lean_dec(v___x_4359_);
v___x_4371_ = lean_box(0);
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4347_;
v___y_4319_ = v_o_4350_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v_args_4322_ = v___x_4371_;
v___y_4323_ = v___y_4351_;
v___y_4324_ = v___y_4352_;
v___y_4325_ = v___y_4353_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4356_;
v___y_4329_ = v___y_4357_;
v___y_4330_ = v___y_4358_;
goto v___jp_4316_;
}
}
v___jp_4372_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4382_ = lean_unsigned_to_nat(2u);
v___x_4383_ = l_Lean_Syntax_getArg(v_stx_3946_, v___x_4382_);
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3950_);
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
v___x_4385_ = l_Lean_Name_mkStr4(v___x_3948_, v___x_3949_, v___x_3950_, v___x_4384_);
lean_inc(v___x_4383_);
v___x_4386_ = l_Lean_Syntax_isOfKind(v___x_4383_, v___x_4385_);
lean_dec(v___x_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; 
lean_dec(v___x_4383_);
lean_dec(v_bang_4373_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4387_;
}
else
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4388_ = l_Lean_Syntax_getArg(v___x_4383_, v___x_3961_);
v___x_4389_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3950_);
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
v___x_4390_ = l_Lean_Name_mkStr4(v___x_3948_, v___x_3949_, v___x_3950_, v___x_4389_);
lean_inc(v___x_4388_);
v___x_4391_ = l_Lean_Syntax_isOfKind(v___x_4388_, v___x_4390_);
lean_dec(v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; 
lean_dec(v___x_4388_);
lean_dec(v___x_4383_);
lean_dec(v_bang_4373_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4392_;
}
else
{
lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4393_ = l_Lean_Syntax_getArg(v___x_4383_, v___x_4343_);
v___x_4394_ = l_Lean_Syntax_isNone(v___x_4393_);
if (v___x_4394_ == 0)
{
uint8_t v___x_4395_; 
lean_inc(v___x_4393_);
v___x_4395_ = l_Lean_Syntax_matchesNull(v___x_4393_, v___x_4343_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_dec(v___x_4393_);
lean_dec(v___x_4388_);
lean_dec(v___x_4383_);
lean_dec(v_bang_4373_);
lean_dec(v_tk_3962_);
lean_dec_ref(v___x_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
v___x_4396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4396_;
}
else
{
lean_object* v_o_4397_; lean_object* v___x_4398_; 
v_o_4397_ = l_Lean_Syntax_getArg(v___x_4393_, v___x_3961_);
lean_dec(v___x_4393_);
v___x_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_o_4397_);
v___y_4345_ = v_bang_4373_;
v___y_4346_ = v___x_4382_;
v___y_4347_ = v___x_4391_;
v___y_4348_ = v___x_4383_;
v___y_4349_ = v___x_4388_;
v_o_4350_ = v___x_4398_;
v___y_4351_ = v___y_4374_;
v___y_4352_ = v___y_4375_;
v___y_4353_ = v___y_4376_;
v___y_4354_ = v___y_4377_;
v___y_4355_ = v___y_4378_;
v___y_4356_ = v___y_4379_;
v___y_4357_ = v___y_4380_;
v___y_4358_ = v___y_4381_;
goto v___jp_4344_;
}
}
else
{
lean_object* v___x_4399_; 
lean_dec(v___x_4393_);
v___x_4399_ = lean_box(0);
v___y_4345_ = v_bang_4373_;
v___y_4346_ = v___x_4382_;
v___y_4347_ = v___x_4391_;
v___y_4348_ = v___x_4383_;
v___y_4349_ = v___x_4388_;
v_o_4350_ = v___x_4399_;
v___y_4351_ = v___y_4374_;
v___y_4352_ = v___y_4375_;
v___y_4353_ = v___y_4376_;
v___y_4354_ = v___y_4377_;
v___y_4355_ = v___y_4378_;
v___y_4356_ = v___y_4379_;
v___y_4357_ = v___y_4380_;
v___y_4358_ = v___y_4381_;
goto v___jp_4344_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4407_, lean_object* v_stx_4408_, lean_object* v___x_4409_, lean_object* v___x_4410_, lean_object* v___x_4411_, lean_object* v___x_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v___x_10541__boxed_4422_; uint8_t v___x_10542__boxed_4423_; lean_object* v_res_4424_; 
v___x_10541__boxed_4422_ = lean_unbox(v___x_4407_);
v___x_10542__boxed_4423_ = lean_unbox(v___x_4409_);
v_res_4424_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10541__boxed_4422_, v_stx_4408_, v___x_10542__boxed_4423_, v___x_4410_, v___x_4411_, v___x_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v_stx_4408_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; uint8_t v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___y_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4444_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4431_);
v___x_4445_ = l_Lean_Syntax_isOfKind(v_stx_4431_, v___x_4444_);
v___x_4446_ = 1;
v___x_4447_ = lean_box(v___x_4445_);
v___x_4448_ = lean_box(v___x_4446_);
v___y_4449_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4449_, 0, v___x_4447_);
lean_closure_set(v___y_4449_, 1, v_stx_4431_);
lean_closure_set(v___y_4449_, 2, v___x_4448_);
lean_closure_set(v___y_4449_, 3, v___x_4441_);
lean_closure_set(v___y_4449_, 4, v___x_4442_);
lean_closure_set(v___y_4449_, 5, v___x_4443_);
v___x_4450_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4450_, 0, v___y_4449_);
v___x_4451_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4450_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4470_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4471_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4473_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4474_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4470_, v___x_4471_, v___x_4472_, v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4505_ = l_Lean_addBuiltinDeclarationRanges(v___x_4503_, v___x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4507_;
}
}
lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
