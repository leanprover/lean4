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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t v___x_33723__boxed_208_; lean_object* v_res_209_; 
v___x_33723__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33723__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_33750__boxed_246_; lean_object* v_res_247_; 
v___x_33750__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33750__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
v___x_257_ = l_Array_mkArray0(lean_box(0));
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
v_ref_266_ = lean_ctor_get(v___y_261_, 4);
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
lean_object* v_options_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_options_311_ = lean_ctor_get(v___y_309_, 1);
v___x_312_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_311_, v_opt_308_);
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
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v_mctx_328_; lean_object* v_lctx_329_; lean_object* v_options_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = lean_st_ref_get(v___y_321_);
v_mctx_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_mctx_328_);
lean_dec(v___x_327_);
v_lctx_329_ = lean_ctor_get(v___y_320_, 2);
v_options_330_ = lean_ctor_get(v___y_322_, 1);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_lctx_329_);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_env_326_);
lean_ctor_set(v___x_331_, 1, v_mctx_328_);
lean_ctor_set(v___x_331_, 2, v_lctx_329_);
lean_ctor_set(v___x_331_, 3, v_options_330_);
v___x_332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_msgData_319_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_348_, uint8_t v___y_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 1)
{
lean_object* v_pre_351_; 
v_pre_351_ = lean_ctor_get(v_x_350_, 0);
switch(lean_obj_tag(v_pre_351_))
{
case 1:
{
lean_object* v_pre_352_; 
v_pre_352_ = lean_ctor_get(v_pre_351_, 0);
switch(lean_obj_tag(v_pre_352_))
{
case 0:
{
lean_object* v_str_353_; lean_object* v_str_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_str_353_ = lean_ctor_get(v_x_350_, 1);
v_str_354_ = lean_ctor_get(v_pre_351_, 1);
v___x_355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_356_ = lean_string_dec_eq(v_str_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_358_ = lean_string_dec_eq(v_str_354_, v___x_357_);
if (v___x_358_ == 0)
{
return v___x_358_;
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_360_ = lean_string_dec_eq(v_str_353_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_360_;
}
else
{
return v_suppressElabErrors_348_;
}
}
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_362_ = lean_string_dec_eq(v_str_353_, v___x_361_);
if (v___x_362_ == 0)
{
return v___x_362_;
}
else
{
return v_suppressElabErrors_348_;
}
}
}
case 1:
{
lean_object* v_pre_363_; 
v_pre_363_ = lean_ctor_get(v_pre_352_, 0);
if (lean_obj_tag(v_pre_363_) == 0)
{
lean_object* v_str_364_; lean_object* v_str_365_; lean_object* v_str_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_str_364_ = lean_ctor_get(v_x_350_, 1);
v_str_365_ = lean_ctor_get(v_pre_351_, 1);
v_str_366_ = lean_ctor_get(v_pre_352_, 1);
v___x_367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_368_ = lean_string_dec_eq(v_str_366_, v___x_367_);
if (v___x_368_ == 0)
{
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_370_ = lean_string_dec_eq(v_str_365_, v___x_369_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_372_ = lean_string_dec_eq(v_str_364_, v___x_371_);
if (v___x_372_ == 0)
{
return v___x_372_;
}
else
{
return v_suppressElabErrors_348_;
}
}
}
}
else
{
return v___y_349_;
}
}
default: 
{
return v___y_349_;
}
}
}
case 0:
{
lean_object* v_str_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_str_373_ = lean_ctor_get(v_x_350_, 1);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_375_ = lean_string_dec_eq(v_str_373_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_348_;
}
}
default: 
{
return v___y_349_;
}
}
}
else
{
return v___y_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_376_, lean_object* v___y_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_suppressElabErrors_boxed_379_; uint8_t v___y_33949__boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_suppressElabErrors_boxed_379_ = lean_unbox(v_suppressElabErrors_376_);
v___y_33949__boxed_380_ = lean_unbox(v___y_377_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_379_, v___y_33949__boxed_380_, v_x_378_);
lean_dec(v_x_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___y_394_; lean_object* v___y_395_; uint8_t v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_430_; uint8_t v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; uint8_t v___y_435_; lean_object* v___y_436_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; uint8_t v___x_476_; lean_object* v___y_478_; uint8_t v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; uint8_t v___y_483_; uint8_t v___y_485_; uint8_t v___x_499_; 
v___x_476_ = 2;
v___x_499_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_476_);
if (v___x_499_ == 0)
{
v___y_485_ = v___x_499_;
goto v___jp_484_;
}
else
{
uint8_t v___x_500_; 
lean_inc_ref(v_msgData_385_);
v___x_500_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_385_);
v___y_485_ = v___x_500_;
goto v___jp_484_;
}
v___jp_393_:
{
lean_object* v___x_403_; lean_object* v_currNamespace_404_; lean_object* v_openDecls_405_; lean_object* v_env_406_; lean_object* v_nextMacroScope_407_; lean_object* v_ngen_408_; lean_object* v_auxDeclNGen_409_; lean_object* v_traceState_410_; lean_object* v_cache_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_428_; 
v___x_403_ = lean_st_ref_take(v___y_402_);
v_currNamespace_404_ = lean_ctor_get(v___y_401_, 5);
v_openDecls_405_ = lean_ctor_get(v___y_401_, 6);
v_env_406_ = lean_ctor_get(v___x_403_, 0);
v_nextMacroScope_407_ = lean_ctor_get(v___x_403_, 1);
v_ngen_408_ = lean_ctor_get(v___x_403_, 2);
v_auxDeclNGen_409_ = lean_ctor_get(v___x_403_, 3);
v_traceState_410_ = lean_ctor_get(v___x_403_, 4);
v_cache_411_ = lean_ctor_get(v___x_403_, 5);
v_messages_412_ = lean_ctor_get(v___x_403_, 6);
v_infoState_413_ = lean_ctor_get(v___x_403_, 7);
v_snapshotTasks_414_ = lean_ctor_get(v___x_403_, 8);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_428_ == 0)
{
v___x_416_ = v___x_403_;
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_messages_412_);
lean_inc(v_cache_411_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_409_);
lean_inc(v_ngen_408_);
lean_inc(v_nextMacroScope_407_);
lean_inc(v_env_406_);
lean_dec(v___x_403_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_inc(v_openDecls_405_);
lean_inc(v_currNamespace_404_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_currNamespace_404_);
lean_ctor_set(v___x_418_, 1, v_openDecls_405_);
v___x_419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___y_397_);
lean_inc_ref(v___y_399_);
lean_inc_ref(v___y_395_);
v___x_420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_420_, 0, v___y_395_);
lean_ctor_set(v___x_420_, 1, v___y_398_);
lean_ctor_set(v___x_420_, 2, v___y_400_);
lean_ctor_set(v___x_420_, 3, v___y_399_);
lean_ctor_set(v___x_420_, 4, v___x_419_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5, v___y_394_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5 + 1, v___y_396_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5 + 2, v_isSilent_387_);
v___x_421_ = l_Lean_MessageLog_add(v___x_420_, v_messages_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 6, v___x_421_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_env_406_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_nextMacroScope_407_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_ngen_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_auxDeclNGen_409_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_traceState_410_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v_cache_411_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_snapshotTasks_414_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_st_ref_put(v___y_402_, v___x_423_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
v___jp_429_:
{
lean_object* v_fileName_437_; lean_object* v_fileMap_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_454_; 
v_fileName_437_ = lean_ctor_get(v___y_432_, 0);
v_fileMap_438_ = lean_ctor_get(v___y_432_, 1);
v___x_439_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_385_);
v___x_440_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_439_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_inc_ref_n(v_fileMap_438_, 2);
v___x_445_ = l_Lean_FileMap_toPosition(v_fileMap_438_, v___y_433_);
lean_dec(v___y_433_);
v___x_446_ = l_Lean_FileMap_toPosition(v_fileMap_438_, v___y_436_);
lean_dec(v___y_436_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
v___x_448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_434_ == 0)
{
lean_del_object(v___x_443_);
lean_dec_ref(v___y_430_);
v___y_394_ = v___y_431_;
v___y_395_ = v_fileName_437_;
v___y_396_ = v___y_435_;
v___y_397_ = v_a_441_;
v___y_398_ = v___x_445_;
v___y_399_ = v___x_448_;
v___y_400_ = v___x_447_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
else
{
uint8_t v___x_449_; 
lean_inc(v_a_441_);
v___x_449_ = l_Lean_MessageData_hasTag(v___y_430_, v_a_441_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec_ref_known(v___x_447_, 1);
lean_dec_ref(v___x_445_);
lean_dec(v_a_441_);
v___x_450_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_450_);
v___x_452_ = v___x_443_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_del_object(v___x_443_);
v___y_394_ = v___y_431_;
v___y_395_ = v_fileName_437_;
v___y_396_ = v___y_435_;
v___y_397_ = v_a_441_;
v___y_398_ = v___x_445_;
v___y_399_ = v___x_448_;
v___y_400_ = v___x_447_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
}
}
}
v___jp_455_:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Syntax_getTailPos_x3f(v___y_457_, v___y_458_);
lean_dec(v___y_457_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_inc(v___y_462_);
v___y_430_ = v___y_456_;
v___y_431_ = v___y_458_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_462_;
v___y_434_ = v___y_460_;
v___y_435_ = v___y_461_;
v___y_436_ = v___y_462_;
goto v___jp_429_;
}
else
{
lean_object* v_val_464_; 
v_val_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___x_463_, 1);
v___y_430_ = v___y_456_;
v___y_431_ = v___y_458_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_462_;
v___y_434_ = v___y_460_;
v___y_435_ = v___y_461_;
v___y_436_ = v_val_464_;
goto v___jp_429_;
}
}
v___jp_465_:
{
lean_object* v_ref_472_; lean_object* v___x_473_; 
v_ref_472_ = l_Lean_replaceRef(v_ref_384_, v___y_470_);
v___x_473_ = l_Lean_Syntax_getPos_x3f(v_ref_472_, v___y_467_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___y_456_ = v___y_466_;
v___y_457_ = v_ref_472_;
v___y_458_ = v___y_467_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_469_;
v___y_461_ = v___y_471_;
v___y_462_ = v___x_474_;
goto v___jp_455_;
}
else
{
lean_object* v_val_475_; 
v_val_475_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_473_, 1);
v___y_456_ = v___y_466_;
v___y_457_ = v_ref_472_;
v___y_458_ = v___y_467_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_469_;
v___y_461_ = v___y_471_;
v___y_462_ = v_val_475_;
goto v___jp_455_;
}
}
v___jp_477_:
{
if (v___y_483_ == 0)
{
v___y_466_ = v___y_481_;
v___y_467_ = v___y_482_;
v___y_468_ = v___y_478_;
v___y_469_ = v___y_479_;
v___y_470_ = v___y_480_;
v___y_471_ = v_severity_386_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___y_481_;
v___y_467_ = v___y_482_;
v___y_468_ = v___y_478_;
v___y_469_ = v___y_479_;
v___y_470_ = v___y_480_;
v___y_471_ = v___x_476_;
goto v___jp_465_;
}
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
lean_object* v_toCold_486_; lean_object* v_options_487_; lean_object* v_ref_488_; uint8_t v_suppressElabErrors_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___f_492_; uint8_t v___x_493_; uint8_t v___x_494_; 
v_toCold_486_ = lean_ctor_get(v___y_390_, 0);
v_options_487_ = lean_ctor_get(v___y_390_, 1);
v_ref_488_ = lean_ctor_get(v___y_390_, 4);
v_suppressElabErrors_489_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*10 + 1);
v___x_490_ = lean_box(v_suppressElabErrors_489_);
v___x_491_ = lean_box(v___y_485_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_492_, 0, v___x_490_);
lean_closure_set(v___f_492_, 1, v___x_491_);
v___x_493_ = 1;
v___x_494_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_478_ = v_toCold_486_;
v___y_479_ = v_suppressElabErrors_489_;
v___y_480_ = v_ref_488_;
v___y_481_ = v___f_492_;
v___y_482_ = v___y_485_;
v___y_483_ = v___x_494_;
goto v___jp_477_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = l_Lean_warningAsError;
v___x_496_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_487_, v___x_495_);
v___y_478_ = v_toCold_486_;
v___y_479_ = v_suppressElabErrors_489_;
v___y_480_ = v_ref_488_;
v___y_481_ = v___f_492_;
v___y_482_ = v___y_485_;
v___y_483_ = v___x_496_;
goto v___jp_477_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_msgData_385_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_501_, lean_object* v_msgData_502_, lean_object* v_severity_503_, lean_object* v_isSilent_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
uint8_t v_severity_boxed_510_; uint8_t v_isSilent_boxed_511_; lean_object* v_res_512_; 
v_severity_boxed_510_ = lean_unbox(v_severity_503_);
v_isSilent_boxed_511_ = lean_unbox(v_isSilent_504_);
v_res_512_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_501_, v_msgData_502_, v_severity_boxed_510_, v_isSilent_boxed_511_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v_ref_501_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_513_, uint8_t v_severity_514_, uint8_t v_isSilent_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_ref_525_; lean_object* v___x_526_; 
v_ref_525_ = lean_ctor_get(v___y_522_, 4);
v___x_526_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_525_, v_msgData_513_, v_severity_514_, v_isSilent_515_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_527_, lean_object* v_severity_528_, lean_object* v_isSilent_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
uint8_t v_severity_boxed_539_; uint8_t v_isSilent_boxed_540_; lean_object* v_res_541_; 
v_severity_boxed_539_ = lean_unbox(v_severity_528_);
v_isSilent_boxed_540_ = lean_unbox(v_isSilent_529_);
v_res_541_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_527_, v_severity_boxed_539_, v_isSilent_boxed_540_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = 1;
v___x_553_ = 0;
v___x_554_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_542_, v___x_552_, v___x_553_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v_env_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_605_; 
v___x_582_ = lean_st_ref_get(v___y_580_);
v_env_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref(v_env_583_);
lean_dec(v___x_582_);
v___x_584_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_585_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_584_, v___y_579_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_605_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint8_t v_isExporting_595_; 
v_isExporting_595_ = lean_ctor_get_uint8(v_env_583_, sizeof(void*)*8);
lean_dec_ref(v_env_583_);
if (v_isExporting_595_ == 0)
{
lean_dec(v_a_586_);
lean_dec(v_id_572_);
goto v___jp_590_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_isPrivateName(v_id_572_);
if (v___x_596_ == 0)
{
lean_dec(v_a_586_);
lean_dec(v_id_572_);
goto v___jp_590_;
}
else
{
uint8_t v___x_597_; 
v___x_597_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_597_ == 0)
{
lean_dec(v_id_572_);
goto v___jp_590_;
}
else
{
lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_del_object(v___x_588_);
v___x_598_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_599_ = 0;
v___x_600_ = l_Lean_MessageData_ofConstName(v_id_572_, v___x_599_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_598_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_603_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_604_;
}
}
}
v___jp_590_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_box(0);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_617_, uint8_t v_enableLog_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v_options_630_; lean_object* v_currNamespace_631_; lean_object* v_openDecls_632_; lean_object* v___x_633_; lean_object* v_env_634_; lean_object* v_res_635_; 
v___x_628_ = lean_st_ref_get(v___y_626_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_628_);
v_options_630_ = lean_ctor_get(v___y_625_, 1);
v_currNamespace_631_ = lean_ctor_get(v___y_625_, 5);
v_openDecls_632_ = lean_ctor_get(v___y_625_, 6);
v___x_633_ = lean_st_ref_get(v___y_626_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
lean_inc(v_openDecls_632_);
lean_inc(v_currNamespace_631_);
v_res_635_ = l_Lean_ResolveName_resolveGlobalName(v_env_629_, v_options_630_, v_currNamespace_631_, v_openDecls_632_, v_id_617_);
if (v_enableLog_618_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_env_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_res_635_);
return v___x_636_;
}
else
{
uint8_t v_isExporting_637_; 
v_isExporting_637_ = lean_ctor_get_uint8(v_env_634_, sizeof(void*)*8);
lean_dec_ref(v_env_634_);
if (v_isExporting_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_res_635_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_635_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v_fst_641_; lean_object* v___x_642_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v_fst_641_ = lean_ctor_get(v_val_640_, 0);
lean_inc(v_fst_641_);
lean_dec(v_val_640_);
v___x_642_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_641_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
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
lean_ctor_set(v___x_644_, 0, v_res_635_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_res_635_);
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
lean_dec(v_res_635_);
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
lean_ctor_set(v___x_659_, 0, v_res_635_);
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
v_ref_709_ = lean_ctor_get(v___y_706_, 4);
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
lean_object* v_toCold_738_; lean_object* v_options_739_; lean_object* v_currRecDepth_740_; lean_object* v_maxRecDepth_741_; lean_object* v_ref_742_; lean_object* v_currNamespace_743_; lean_object* v_openDecls_744_; lean_object* v_initHeartbeats_745_; lean_object* v_maxHeartbeats_746_; lean_object* v_currMacroScope_747_; uint8_t v_diag_748_; uint8_t v_suppressElabErrors_749_; lean_object* v_ref_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_toCold_738_ = lean_ctor_get(v___y_735_, 0);
v_options_739_ = lean_ctor_get(v___y_735_, 1);
v_currRecDepth_740_ = lean_ctor_get(v___y_735_, 2);
v_maxRecDepth_741_ = lean_ctor_get(v___y_735_, 3);
v_ref_742_ = lean_ctor_get(v___y_735_, 4);
v_currNamespace_743_ = lean_ctor_get(v___y_735_, 5);
v_openDecls_744_ = lean_ctor_get(v___y_735_, 6);
v_initHeartbeats_745_ = lean_ctor_get(v___y_735_, 7);
v_maxHeartbeats_746_ = lean_ctor_get(v___y_735_, 8);
v_currMacroScope_747_ = lean_ctor_get(v___y_735_, 9);
v_diag_748_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*10);
v_suppressElabErrors_749_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*10 + 1);
v_ref_750_ = l_Lean_replaceRef(v_ref_727_, v_ref_742_);
lean_inc(v_currMacroScope_747_);
lean_inc(v_maxHeartbeats_746_);
lean_inc(v_initHeartbeats_745_);
lean_inc(v_openDecls_744_);
lean_inc(v_currNamespace_743_);
lean_inc(v_maxRecDepth_741_);
lean_inc(v_currRecDepth_740_);
lean_inc_ref(v_options_739_);
lean_inc_ref(v_toCold_738_);
v___x_751_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_751_, 0, v_toCold_738_);
lean_ctor_set(v___x_751_, 1, v_options_739_);
lean_ctor_set(v___x_751_, 2, v_currRecDepth_740_);
lean_ctor_set(v___x_751_, 3, v_maxRecDepth_741_);
lean_ctor_set(v___x_751_, 4, v_ref_750_);
lean_ctor_set(v___x_751_, 5, v_currNamespace_743_);
lean_ctor_set(v___x_751_, 6, v_openDecls_744_);
lean_ctor_set(v___x_751_, 7, v_initHeartbeats_745_);
lean_ctor_set(v___x_751_, 8, v_maxHeartbeats_746_);
lean_ctor_set(v___x_751_, 9, v_currMacroScope_747_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*10, v_diag_748_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*10 + 1, v_suppressElabErrors_749_);
v___x_752_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_728_, v___y_733_, v___y_734_, v___x_751_, v___y_736_);
lean_dec_ref_known(v___x_751_, 10);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_753_, lean_object* v_msg_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_753_, v_msg_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v_ref_753_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
lean_ctor_set(v___x_770_, 3, v___x_769_);
lean_ctor_set(v___x_770_, 4, v___x_768_);
lean_ctor_set(v___x_770_, 5, v___x_768_);
lean_ctor_set(v___x_770_, 6, v___x_768_);
lean_ctor_set(v___x_770_, 7, v___x_768_);
lean_ctor_set(v___x_770_, 8, v___x_768_);
lean_ctor_set(v___x_770_, 9, v___x_768_);
lean_ctor_set(v___x_770_, 10, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = ((size_t)5ULL);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_unsigned_to_nat(32u);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_776_);
v___x_778_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_779_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_777_);
lean_ctor_set(v___x_779_, 2, v___x_775_);
lean_ctor_set(v___x_779_, 3, v___x_775_);
lean_ctor_set_usize(v___x_779_, 4, v___x_774_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_box(1);
v___x_781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_780_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_805_, lean_object* v_declHint_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v_env_810_; uint8_t v___x_811_; 
v___x_809_ = lean_st_ref_get(v___y_807_);
v_env_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_env_810_);
lean_dec(v___x_809_);
v___x_811_ = l_Lean_Name_isAnonymous(v_declHint_806_);
if (v___x_811_ == 0)
{
uint8_t v_isExporting_812_; 
v_isExporting_812_ = lean_ctor_get_uint8(v_env_810_, sizeof(void*)*8);
if (v_isExporting_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec_ref(v_env_810_);
lean_dec(v_declHint_806_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_msg_805_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; uint8_t v___x_815_; 
lean_inc_ref(v_env_810_);
v___x_814_ = l_Lean_Environment_setExporting(v_env_810_, v___x_811_);
lean_inc(v_declHint_806_);
lean_inc_ref(v___x_814_);
v___x_815_ = l_Lean_Environment_contains(v___x_814_, v_declHint_806_, v_isExporting_812_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v___x_814_);
lean_dec_ref(v_env_810_);
lean_dec(v_declHint_806_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_msg_805_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_c_822_; lean_object* v___x_823_; 
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_819_ = l_Lean_Options_empty;
v___x_820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_820_, 0, v___x_814_);
lean_ctor_set(v___x_820_, 1, v___x_817_);
lean_ctor_set(v___x_820_, 2, v___x_818_);
lean_ctor_set(v___x_820_, 3, v___x_819_);
lean_inc(v_declHint_806_);
v___x_821_ = l_Lean_MessageData_ofConstName(v_declHint_806_, v___x_811_);
v_c_822_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_822_, 0, v___x_820_);
lean_ctor_set(v_c_822_, 1, v___x_821_);
v___x_823_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_810_, v_declHint_806_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v_env_810_);
lean_dec(v_declHint_806_);
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_c_822_);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_MessageData_note(v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v_msg_805_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_866_; 
v_val_831_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_866_ == 0)
{
v___x_833_ = v___x_823_;
v_isShared_834_ = v_isSharedCheck_866_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v___x_823_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_866_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_mod_838_; uint8_t v___x_839_; 
v___x_835_ = lean_box(0);
v___x_836_ = l_Lean_Environment_header(v_env_810_);
lean_dec_ref(v_env_810_);
v___x_837_ = l_Lean_EnvironmentHeader_moduleNames(v___x_836_);
v_mod_838_ = lean_array_get(v___x_835_, v___x_837_, v_val_831_);
lean_dec(v_val_831_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_isPrivateName(v_declHint_806_);
lean_dec(v_declHint_806_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_c_822_);
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Lean_MessageData_ofName(v_mod_838_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_MessageData_note(v___x_847_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v_msg_805_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
lean_ctor_set(v___x_833_, 0, v___x_849_);
v___x_851_ = v___x_833_;
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
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v_c_822_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_MessageData_ofName(v_mod_838_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_MessageData_note(v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v_msg_805_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
lean_ctor_set(v___x_833_, 0, v___x_862_);
v___x_864_ = v___x_833_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_867_; 
lean_dec_ref(v_env_810_);
lean_dec(v_declHint_806_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_msg_805_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_868_, lean_object* v_declHint_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_868_, v_declHint_869_, v___y_870_);
lean_dec(v___y_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_873_, lean_object* v_declHint_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v___x_884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_873_, v_declHint_874_, v___y_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_894_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = l_Lean_unknownIdentifierMessageTag;
v___x_890_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_907_, lean_object* v_msg_908_, lean_object* v_declHint_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
v___x_919_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_908_, v_declHint_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v___x_921_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_907_, v_a_920_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_922_, lean_object* v_msg_923_, lean_object* v_declHint_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_922_, v_msg_923_, v_declHint_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v_ref_922_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_941_, lean_object* v_constName_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_952_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_953_ = 0;
lean_inc(v_constName_942_);
v___x_954_ = l_Lean_MessageData_ofConstName(v_constName_942_, v___x_953_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_941_, v___x_957_, v_constName_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_959_, lean_object* v_constName_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_959_, v_constName_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_ref_959_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_971_, lean_object* v_cs_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_cs_983_; uint8_t v___x_987_; 
v___x_982_ = lean_box(0);
v_cs_983_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_972_, v___x_982_);
v___x_987_ = l_List_isEmpty___redArg(v_cs_983_);
if (v___x_987_ == 0)
{
lean_dec(v_n_971_);
goto v___jp_984_;
}
else
{
lean_object* v_ref_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_cs_983_);
v_ref_988_ = lean_ctor_get(v___y_979_, 4);
v___x_989_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_988_, v_n_971_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_983_, v___x_982_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_998_, lean_object* v_cs_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_998_, v_cs_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = 1;
lean_inc(v_n_1010_);
v___x_1021_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1010_, v___x_1020_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1010_, v_a_1022_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1023_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_n_1010_);
v_a_1024_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1021_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
if (lean_obj_tag(v_a_1043_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_array_to_list(v_a_1044_);
return v___x_1045_;
}
else
{
lean_object* v_head_1046_; 
v_head_1046_ = lean_ctor_get(v_a_1043_, 0);
if (lean_obj_tag(v_head_1046_) == 1)
{
lean_object* v_fields_1047_; 
v_fields_1047_ = lean_ctor_get(v_head_1046_, 1);
if (lean_obj_tag(v_fields_1047_) == 0)
{
lean_object* v_tail_1048_; lean_object* v_n_1049_; lean_object* v___x_1050_; 
lean_inc_ref(v_head_1046_);
v_tail_1048_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_tail_1048_);
lean_dec_ref_known(v_a_1043_, 2);
v_n_1049_ = lean_ctor_get(v_head_1046_, 0);
lean_inc(v_n_1049_);
lean_dec_ref_known(v_head_1046_, 2);
v___x_1050_ = lean_array_push(v_a_1044_, v_n_1049_);
v_a_1043_ = v_tail_1048_;
v_a_1044_ = v___x_1050_;
goto _start;
}
else
{
lean_object* v_tail_1052_; 
v_tail_1052_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_tail_1052_);
lean_dec_ref_known(v_a_1043_, 2);
v_a_1043_ = v_tail_1052_;
goto _start;
}
}
else
{
lean_object* v_tail_1054_; 
v_tail_1054_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_tail_1054_);
lean_dec_ref_known(v_a_1043_, 2);
v_a_1043_ = v_tail_1054_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1062_ = l_Lean_MessageData_ofFormat(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1063_, lean_object* v_k_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
if (lean_obj_tag(v_stx_1063_) == 3)
{
lean_object* v_val_1074_; lean_object* v_preresolved_1075_; lean_object* v___x_1076_; lean_object* v_pre_1077_; uint8_t v___x_1078_; 
v_val_1074_ = lean_ctor_get(v_stx_1063_, 2);
lean_inc(v_val_1074_);
v_preresolved_1075_ = lean_ctor_get(v_stx_1063_, 3);
v___x_1076_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1075_);
v_pre_1077_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1075_, v___x_1076_);
v___x_1078_ = l_List_isEmpty___redArg(v_pre_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_val_1074_);
lean_dec_ref_known(v_stx_1063_, 4);
lean_dec_ref(v_k_1064_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_pre_1077_);
return v___x_1079_;
}
else
{
lean_object* v_toCold_1080_; lean_object* v_options_1081_; lean_object* v_currRecDepth_1082_; lean_object* v_maxRecDepth_1083_; lean_object* v_ref_1084_; lean_object* v_currNamespace_1085_; lean_object* v_openDecls_1086_; lean_object* v_initHeartbeats_1087_; lean_object* v_maxHeartbeats_1088_; lean_object* v_currMacroScope_1089_; uint8_t v_diag_1090_; uint8_t v_suppressElabErrors_1091_; lean_object* v_ref_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v_pre_1077_);
v_toCold_1080_ = lean_ctor_get(v___y_1071_, 0);
v_options_1081_ = lean_ctor_get(v___y_1071_, 1);
v_currRecDepth_1082_ = lean_ctor_get(v___y_1071_, 2);
v_maxRecDepth_1083_ = lean_ctor_get(v___y_1071_, 3);
v_ref_1084_ = lean_ctor_get(v___y_1071_, 4);
v_currNamespace_1085_ = lean_ctor_get(v___y_1071_, 5);
v_openDecls_1086_ = lean_ctor_get(v___y_1071_, 6);
v_initHeartbeats_1087_ = lean_ctor_get(v___y_1071_, 7);
v_maxHeartbeats_1088_ = lean_ctor_get(v___y_1071_, 8);
v_currMacroScope_1089_ = lean_ctor_get(v___y_1071_, 9);
v_diag_1090_ = lean_ctor_get_uint8(v___y_1071_, sizeof(void*)*10);
v_suppressElabErrors_1091_ = lean_ctor_get_uint8(v___y_1071_, sizeof(void*)*10 + 1);
v_ref_1092_ = l_Lean_replaceRef(v_stx_1063_, v_ref_1084_);
lean_dec_ref_known(v_stx_1063_, 4);
lean_inc(v_currMacroScope_1089_);
lean_inc(v_maxHeartbeats_1088_);
lean_inc(v_initHeartbeats_1087_);
lean_inc(v_openDecls_1086_);
lean_inc(v_currNamespace_1085_);
lean_inc(v_maxRecDepth_1083_);
lean_inc(v_currRecDepth_1082_);
lean_inc_ref(v_options_1081_);
lean_inc_ref(v_toCold_1080_);
v___x_1093_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1093_, 0, v_toCold_1080_);
lean_ctor_set(v___x_1093_, 1, v_options_1081_);
lean_ctor_set(v___x_1093_, 2, v_currRecDepth_1082_);
lean_ctor_set(v___x_1093_, 3, v_maxRecDepth_1083_);
lean_ctor_set(v___x_1093_, 4, v_ref_1092_);
lean_ctor_set(v___x_1093_, 5, v_currNamespace_1085_);
lean_ctor_set(v___x_1093_, 6, v_openDecls_1086_);
lean_ctor_set(v___x_1093_, 7, v_initHeartbeats_1087_);
lean_ctor_set(v___x_1093_, 8, v_maxHeartbeats_1088_);
lean_ctor_set(v___x_1093_, 9, v_currMacroScope_1089_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*10, v_diag_1090_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*10 + 1, v_suppressElabErrors_1091_);
lean_inc(v___y_1072_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
v___x_1094_ = lean_apply_10(v_k_1064_, v_val_1074_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___x_1093_, v___y_1072_, lean_box(0));
return v___x_1094_;
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v_k_1064_);
v___x_1095_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1096_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1063_, v___x_1095_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v_stx_1063_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1097_, lean_object* v_k_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1097_, v_k_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1121_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1110_, v___x_1120_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1133_, size_t v_sz_1134_, size_t v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1135_, v_sz_1134_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_b_1136_);
return v___x_1147_;
}
else
{
lean_object* v_a_1148_; lean_object* v_name_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_a_1148_ = lean_array_uget_borrowed(v_as_1133_, v_i_1135_);
v_name_1149_ = lean_ctor_get(v_a_1148_, 0);
lean_inc(v_name_1149_);
v___x_1150_ = l_Lean_mkIdent(v_name_1149_);
lean_inc(v___x_1150_);
v___x_1151_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1150_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1150_, v_a_1152_, v_b_1136_, v___y_1143_);
lean_dec(v_a_1152_);
lean_dec(v___x_1150_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; size_t v___x_1155_; size_t v___x_1156_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1135_, v___x_1155_);
v_i_1135_ = v___x_1156_;
v_b_1136_ = v_a_1154_;
goto _start;
}
else
{
return v___x_1153_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v___x_1150_);
lean_dec_ref(v_b_1136_);
v_a_1158_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1151_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1151_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1166_, lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1166_, v_sz_boxed_1179_, v_i_boxed_1180_, v_b_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_as_1166_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1201_, lean_object* v_stx_1202_, uint8_t v___x_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v___f_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
if (v___x_1201_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_1217_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v_tk_1219_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1291_; uint8_t v___y_1292_; uint8_t v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v_stxForSuggestion_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; uint8_t v___y_1335_; uint8_t v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; uint8_t v___y_1461_; uint8_t v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; uint8_t v___y_1500_; lean_object* v___y_1501_; uint8_t v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; uint8_t v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; uint8_t v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; uint8_t v___y_1540_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; uint8_t v___y_1556_; uint8_t v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v_stxForExecution_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; uint8_t v___y_1670_; lean_object* v___y_1671_; uint8_t v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; uint8_t v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; uint8_t v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; uint8_t v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1822_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_argsArray_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; uint8_t v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_args_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___x_2017_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v_o_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v_bang_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v_tk_1219_ = l_Lean_Syntax_getArg(v_stx_1202_, v___x_1218_);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2076_ = l_Lean_Syntax_getArg(v_stx_1202_, v___x_2017_);
v___x_2077_ = l_Lean_Syntax_isNone(v___x_2076_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
lean_inc(v___x_2076_);
v___x_2078_ = l_Lean_Syntax_matchesNull(v___x_2076_, v___x_2017_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec(v___x_2076_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2079_;
}
else
{
lean_object* v_bang_2080_; lean_object* v___x_2081_; 
v_bang_2080_ = l_Lean_Syntax_getArg(v___x_2076_, v___x_1218_);
lean_dec(v___x_2076_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_bang_2080_);
v_bang_2048_ = v___x_2081_;
v___y_2049_ = v___y_1208_;
v___y_2050_ = v___y_1209_;
v___y_2051_ = v___y_1210_;
v___y_2052_ = v___y_1211_;
v___y_2053_ = v___y_1212_;
v___y_2054_ = v___y_1213_;
v___y_2055_ = v___y_1214_;
v___y_2056_ = v___y_1215_;
goto v___jp_2047_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec(v___x_2076_);
v___x_2082_ = lean_box(0);
v_bang_2048_ = v___x_2082_;
v___y_2049_ = v___y_1208_;
v___y_2050_ = v___y_1209_;
v___y_2051_ = v___y_1210_;
v___y_2052_ = v___y_1211_;
v___y_2053_ = v___y_1212_;
v___y_2054_ = v___y_1213_;
v___y_2055_ = v___y_1214_;
v___y_2056_ = v___y_1215_;
goto v___jp_2047_;
}
v___jp_1220_:
{
lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(v___x_1203_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1235_, 0, v___y_1222_);
lean_closure_set(v___f_1235_, 1, v___x_1218_);
lean_closure_set(v___f_1235_, 2, v___x_1234_);
lean_closure_set(v___f_1235_, 3, v___y_1233_);
lean_closure_set(v___f_1235_, 4, v___y_1223_);
v___x_1236_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1221_, v___f_1235_, v___y_1224_, v___y_1228_, v___y_1226_, v___y_1231_, v___y_1232_, v___y_1229_, v___y_1230_, v___y_1225_);
lean_dec(v___y_1221_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v_usedTheorems_1238_; lean_object* v_diag_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1281_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_usedTheorems_1238_ = lean_ctor_get(v_a_1237_, 0);
v_diag_1239_ = lean_ctor_get(v_a_1237_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_a_1237_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1241_ = v_a_1237_;
v_isShared_1242_ = v_isSharedCheck_1281_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_diag_1239_);
lean_inc(v_usedTheorems_1238_);
lean_dec(v_a_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1281_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1227_, v_usedTheorems_1238_, v___y_1232_, v___y_1229_, v___y_1230_, v___y_1225_);
lean_dec_ref(v_usedTheorems_1238_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_ref_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v_ref_1245_ = lean_ctor_get(v___y_1230_, 4);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_a_1244_);
lean_ctor_set(v___x_1241_, 0, v___x_1246_);
v___x_1248_ = v___x_1241_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1244_);
v___x_1248_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
lean_ctor_set(v___x_1250_, 3, v___x_1249_);
lean_ctor_set(v___x_1250_, 4, v___x_1249_);
lean_ctor_set(v___x_1250_, 5, v___x_1249_);
lean_inc(v_ref_1245_);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_ref_1245_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1253_ = 4;
v___x_1254_ = l_Lean_MessageData_nil;
v___x_1255_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1219_, v___x_1250_, v___x_1251_, v___x_1252_, v___x_1249_, v___x_1253_, v___x_1254_, v___y_1230_, v___y_1225_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1263_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_diag_1239_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_diag_1239_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_diag_1239_);
v_a_1264_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1255_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1255_);
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
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_del_object(v___x_1241_);
lean_dec_ref(v_diag_1239_);
lean_dec(v_tk_1219_);
v_a_1273_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1243_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1243_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v___y_1227_);
lean_dec(v_tk_1219_);
v_a_1282_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1236_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1236_);
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
v___jp_1290_:
{
uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = 0;
v___x_1306_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1307_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1294_, v___x_1305_, v___y_1292_, v___x_1305_, v___x_1306_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1294_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
if (lean_obj_tag(v___y_1295_) == 0)
{
lean_object* v_ctx_1309_; lean_object* v_simprocs_1310_; lean_object* v_dischargeWrapper_1311_; 
v_ctx_1309_ = lean_ctor_get(v_a_1308_, 0);
lean_inc_ref(v_ctx_1309_);
v_simprocs_1310_ = lean_ctor_get(v_a_1308_, 1);
lean_inc_ref(v_simprocs_1310_);
v_dischargeWrapper_1311_ = lean_ctor_get(v_a_1308_, 2);
lean_inc(v_dischargeWrapper_1311_);
lean_dec(v_a_1308_);
v___y_1221_ = v_dischargeWrapper_1311_;
v___y_1222_ = v___y_1291_;
v___y_1223_ = v_simprocs_1310_;
v___y_1224_ = v___y_1297_;
v___y_1225_ = v___y_1304_;
v___y_1226_ = v___y_1299_;
v___y_1227_ = v_stxForSuggestion_1296_;
v___y_1228_ = v___y_1298_;
v___y_1229_ = v___y_1302_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1300_;
v___y_1232_ = v___y_1301_;
v___y_1233_ = v_ctx_1309_;
goto v___jp_1220_;
}
else
{
lean_dec_ref_known(v___y_1295_, 1);
if (v___y_1293_ == 0)
{
lean_object* v_ctx_1312_; lean_object* v_simprocs_1313_; lean_object* v_dischargeWrapper_1314_; 
v_ctx_1312_ = lean_ctor_get(v_a_1308_, 0);
lean_inc_ref(v_ctx_1312_);
v_simprocs_1313_ = lean_ctor_get(v_a_1308_, 1);
lean_inc_ref(v_simprocs_1313_);
v_dischargeWrapper_1314_ = lean_ctor_get(v_a_1308_, 2);
lean_inc(v_dischargeWrapper_1314_);
lean_dec(v_a_1308_);
v___y_1221_ = v_dischargeWrapper_1314_;
v___y_1222_ = v___y_1291_;
v___y_1223_ = v_simprocs_1313_;
v___y_1224_ = v___y_1297_;
v___y_1225_ = v___y_1304_;
v___y_1226_ = v___y_1299_;
v___y_1227_ = v_stxForSuggestion_1296_;
v___y_1228_ = v___y_1298_;
v___y_1229_ = v___y_1302_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1300_;
v___y_1232_ = v___y_1301_;
v___y_1233_ = v_ctx_1312_;
goto v___jp_1220_;
}
else
{
lean_object* v_ctx_1315_; lean_object* v_simprocs_1316_; lean_object* v_dischargeWrapper_1317_; lean_object* v___x_1318_; 
v_ctx_1315_ = lean_ctor_get(v_a_1308_, 0);
lean_inc_ref(v_ctx_1315_);
v_simprocs_1316_ = lean_ctor_get(v_a_1308_, 1);
lean_inc_ref(v_simprocs_1316_);
v_dischargeWrapper_1317_ = lean_ctor_get(v_a_1308_, 2);
lean_inc(v_dischargeWrapper_1317_);
lean_dec(v_a_1308_);
v___x_1318_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1315_);
v___y_1221_ = v_dischargeWrapper_1317_;
v___y_1222_ = v___y_1291_;
v___y_1223_ = v_simprocs_1316_;
v___y_1224_ = v___y_1297_;
v___y_1225_ = v___y_1304_;
v___y_1226_ = v___y_1299_;
v___y_1227_ = v_stxForSuggestion_1296_;
v___y_1228_ = v___y_1298_;
v___y_1229_ = v___y_1302_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1300_;
v___y_1232_ = v___y_1301_;
v___y_1233_ = v___x_1318_;
goto v___jp_1220_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_stxForSuggestion_1296_);
lean_dec(v___y_1295_);
lean_dec(v___y_1291_);
lean_dec(v_tk_1219_);
v_a_1319_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1307_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1307_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_inc_ref(v___y_1330_);
v___x_1351_ = l_Array_append___redArg(v___y_1330_, v___y_1350_);
lean_dec_ref(v___y_1350_);
lean_inc(v___y_1345_);
lean_inc(v___y_1341_);
v___x_1352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1352_, 0, v___y_1341_);
lean_ctor_set(v___x_1352_, 1, v___y_1345_);
lean_ctor_set(v___x_1352_, 2, v___x_1351_);
v___x_1353_ = l_Lean_Syntax_node6(v___y_1341_, v___y_1344_, v___y_1346_, v___y_1329_, v___y_1334_, v___y_1331_, v___y_1349_, v___x_1352_);
v___y_1291_ = v___y_1328_;
v___y_1292_ = v___y_1335_;
v___y_1293_ = v___y_1336_;
v___y_1294_ = v___y_1343_;
v___y_1295_ = v___y_1347_;
v_stxForSuggestion_1296_ = v___x_1353_;
v___y_1297_ = v___y_1338_;
v___y_1298_ = v___y_1342_;
v___y_1299_ = v___y_1340_;
v___y_1300_ = v___y_1333_;
v___y_1301_ = v___y_1339_;
v___y_1302_ = v___y_1348_;
v___y_1303_ = v___y_1337_;
v___y_1304_ = v___y_1332_;
goto v___jp_1290_;
}
v___jp_1354_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_inc_ref_n(v___y_1358_, 2);
v___x_1378_ = l_Array_append___redArg(v___y_1358_, v___y_1377_);
lean_dec_ref(v___y_1377_);
lean_inc_n(v___y_1373_, 3);
lean_inc_n(v___y_1370_, 5);
v___x_1379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1370_);
lean_ctor_set(v___x_1379_, 1, v___y_1373_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1370_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1383_ = l_Lean_Syntax_SepArray_ofElems(v___x_1382_, v___y_1357_);
lean_dec_ref(v___y_1357_);
v___x_1384_ = l_Array_append___redArg(v___y_1358_, v___x_1383_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1370_);
lean_ctor_set(v___x_1385_, 1, v___y_1373_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1370_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_Syntax_node3(v___y_1370_, v___y_1373_, v___x_1381_, v___x_1385_, v___x_1387_);
if (lean_obj_tag(v___y_1362_) == 1)
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
v_val_1389_ = lean_ctor_get(v___y_1362_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___y_1362_, 1);
v___x_1390_ = l_Array_mkArray1___redArg(v_val_1389_);
v___y_1328_ = v___y_1355_;
v___y_1329_ = v___y_1356_;
v___y_1330_ = v___y_1358_;
v___y_1331_ = v___x_1379_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1365_;
v___y_1338_ = v___y_1366_;
v___y_1339_ = v___y_1368_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1370_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v___y_1372_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1376_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___x_1388_;
v___y_1350_ = v___x_1390_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v___y_1362_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1328_ = v___y_1355_;
v___y_1329_ = v___y_1356_;
v___y_1330_ = v___y_1358_;
v___y_1331_ = v___x_1379_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1365_;
v___y_1338_ = v___y_1366_;
v___y_1339_ = v___y_1368_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1370_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v___y_1372_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1376_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___x_1388_;
v___y_1350_ = v___x_1391_;
goto v___jp_1327_;
}
}
v___jp_1392_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_inc_ref(v___y_1397_);
v___x_1416_ = l_Array_append___redArg(v___y_1397_, v___y_1415_);
lean_dec_ref(v___y_1415_);
lean_inc(v___y_1411_);
lean_inc(v___y_1408_);
v___x_1417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1417_, 0, v___y_1408_);
lean_ctor_set(v___x_1417_, 1, v___y_1411_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
if (lean_obj_tag(v___y_1396_) == 1)
{
lean_object* v_val_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_val_1418_ = lean_ctor_get(v___y_1396_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v___y_1396_, 1);
v___x_1419_ = l_Lean_SourceInfo_fromRef(v_val_1418_, v___x_1203_);
lean_dec(v_val_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Array_mkArray1___redArg(v___x_1421_);
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___y_1394_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1397_;
v___y_1359_ = v___y_1398_;
v___y_1360_ = v___y_1399_;
v___y_1361_ = v___x_1417_;
v___y_1362_ = v___y_1400_;
v___y_1363_ = v___y_1401_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1406_;
v___y_1368_ = v___y_1405_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___x_1422_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1423_; 
lean_dec(v___y_1396_);
v___x_1423_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___y_1394_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1397_;
v___y_1359_ = v___y_1398_;
v___y_1360_ = v___y_1399_;
v___y_1361_ = v___x_1417_;
v___y_1362_ = v___y_1400_;
v___y_1363_ = v___y_1401_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1406_;
v___y_1368_ = v___y_1405_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___x_1423_;
goto v___jp_1354_;
}
}
v___jp_1424_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_inc_ref(v___y_1444_);
v___x_1448_ = l_Array_append___redArg(v___y_1444_, v___y_1447_);
lean_dec_ref(v___y_1447_);
lean_inc(v___y_1427_);
lean_inc(v___y_1428_);
v___x_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1428_);
lean_ctor_set(v___x_1449_, 1, v___y_1427_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = l_Lean_Syntax_node6(v___y_1428_, v___y_1436_, v___y_1431_, v___y_1426_, v___y_1441_, v___y_1437_, v___y_1438_, v___x_1449_);
v___y_1291_ = v___y_1425_;
v___y_1292_ = v___y_1432_;
v___y_1293_ = v___y_1433_;
v___y_1294_ = v___y_1443_;
v___y_1295_ = v___y_1445_;
v_stxForSuggestion_1296_ = v___x_1450_;
v___y_1297_ = v___y_1435_;
v___y_1298_ = v___y_1442_;
v___y_1299_ = v___y_1440_;
v___y_1300_ = v___y_1430_;
v___y_1301_ = v___y_1439_;
v___y_1302_ = v___y_1446_;
v___y_1303_ = v___y_1434_;
v___y_1304_ = v___y_1429_;
goto v___jp_1290_;
}
v___jp_1451_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc_ref_n(v___y_1471_, 2);
v___x_1475_ = l_Array_append___redArg(v___y_1471_, v___y_1474_);
lean_dec_ref(v___y_1474_);
lean_inc_n(v___y_1454_, 3);
lean_inc_n(v___y_1456_, 5);
v___x_1476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1456_);
lean_ctor_set(v___x_1476_, 1, v___y_1454_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1456_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1480_ = l_Lean_Syntax_SepArray_ofElems(v___x_1479_, v___y_1455_);
lean_dec_ref(v___y_1455_);
v___x_1481_ = l_Array_append___redArg(v___y_1471_, v___x_1480_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___y_1456_);
lean_ctor_set(v___x_1482_, 1, v___y_1454_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1456_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_Syntax_node3(v___y_1456_, v___y_1454_, v___x_1478_, v___x_1482_, v___x_1484_);
if (lean_obj_tag(v___y_1460_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
v_val_1486_ = lean_ctor_get(v___y_1460_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___y_1460_, 1);
v___x_1487_ = l_Array_mkArray1___redArg(v_val_1486_);
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1453_;
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1456_;
v___y_1429_ = v___y_1457_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1459_;
v___y_1432_ = v___y_1461_;
v___y_1433_ = v___y_1462_;
v___y_1434_ = v___y_1463_;
v___y_1435_ = v___y_1464_;
v___y_1436_ = v___y_1465_;
v___y_1437_ = v___x_1476_;
v___y_1438_ = v___x_1485_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___x_1487_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v___y_1460_);
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1453_;
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1456_;
v___y_1429_ = v___y_1457_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1459_;
v___y_1432_ = v___y_1461_;
v___y_1433_ = v___y_1462_;
v___y_1434_ = v___y_1463_;
v___y_1435_ = v___y_1464_;
v___y_1436_ = v___y_1465_;
v___y_1437_ = v___x_1476_;
v___y_1438_ = v___x_1485_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___x_1488_;
goto v___jp_1424_;
}
}
v___jp_1489_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_inc_ref(v___y_1509_);
v___x_1513_ = l_Array_append___redArg(v___y_1509_, v___y_1512_);
lean_dec_ref(v___y_1512_);
lean_inc(v___y_1492_);
lean_inc(v___y_1495_);
v___x_1514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1514_, 0, v___y_1495_);
lean_ctor_set(v___x_1514_, 1, v___y_1492_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
if (lean_obj_tag(v___y_1494_) == 1)
{
lean_object* v_val_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_val_1515_ = lean_ctor_get(v___y_1494_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v___y_1494_, 1);
v___x_1516_ = l_Lean_SourceInfo_fromRef(v_val_1515_, v___x_1203_);
lean_dec(v_val_1515_);
v___x_1517_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Array_mkArray1___redArg(v___x_1518_);
v___y_1452_ = v___y_1490_;
v___y_1453_ = v___y_1491_;
v___y_1454_ = v___y_1492_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1502_;
v___y_1463_ = v___y_1503_;
v___y_1464_ = v___y_1501_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1506_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___x_1514_;
v___y_1470_ = v___y_1508_;
v___y_1471_ = v___y_1509_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___x_1519_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1520_; 
lean_dec(v___y_1494_);
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1452_ = v___y_1490_;
v___y_1453_ = v___y_1491_;
v___y_1454_ = v___y_1492_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1502_;
v___y_1463_ = v___y_1503_;
v___y_1464_ = v___y_1501_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1506_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___x_1514_;
v___y_1470_ = v___y_1508_;
v___y_1471_ = v___y_1509_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___x_1520_;
goto v___jp_1451_;
}
}
v___jp_1521_:
{
lean_object* v_ref_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_ref_1541_ = lean_ctor_get(v___y_1530_, 4);
v___x_1542_ = l_Lean_SourceInfo_fromRef(v_ref_1541_, v___y_1540_);
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1544_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_1543_);
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_tk_1219_, v___x_1203_);
v___x_1546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1543_);
v___x_1547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1548_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1533_) == 1)
{
lean_object* v_val_1549_; lean_object* v___x_1550_; 
v_val_1549_ = lean_ctor_get(v___y_1533_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___y_1533_, 1);
v___x_1550_ = l_Array_mkArray1___redArg(v_val_1549_);
v___y_1490_ = v___y_1522_;
v___y_1491_ = v___y_1523_;
v___y_1492_ = v___x_1547_;
v___y_1493_ = v___y_1524_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___x_1542_;
v___y_1496_ = v___y_1526_;
v___y_1497_ = v___y_1527_;
v___y_1498_ = v___x_1546_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1529_;
v___y_1501_ = v___y_1531_;
v___y_1502_ = v___y_1532_;
v___y_1503_ = v___y_1530_;
v___y_1504_ = v___x_1544_;
v___y_1505_ = v___y_1534_;
v___y_1506_ = v___y_1535_;
v___y_1507_ = v___y_1536_;
v___y_1508_ = v___y_1537_;
v___y_1509_ = v___x_1548_;
v___y_1510_ = v___y_1539_;
v___y_1511_ = v___y_1538_;
v___y_1512_ = v___x_1550_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1551_; 
lean_dec(v___y_1533_);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1490_ = v___y_1522_;
v___y_1491_ = v___y_1523_;
v___y_1492_ = v___x_1547_;
v___y_1493_ = v___y_1524_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___x_1542_;
v___y_1496_ = v___y_1526_;
v___y_1497_ = v___y_1527_;
v___y_1498_ = v___x_1546_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1529_;
v___y_1501_ = v___y_1531_;
v___y_1502_ = v___y_1532_;
v___y_1503_ = v___y_1530_;
v___y_1504_ = v___x_1544_;
v___y_1505_ = v___y_1534_;
v___y_1506_ = v___y_1535_;
v___y_1507_ = v___y_1536_;
v___y_1508_ = v___y_1537_;
v___y_1509_ = v___x_1548_;
v___y_1510_ = v___y_1539_;
v___y_1511_ = v___y_1538_;
v___y_1512_ = v___x_1551_;
goto v___jp_1489_;
}
}
v___jp_1552_:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1555_);
if (lean_obj_tag(v___y_1561_) == 0)
{
lean_object* v_a_1572_; uint8_t v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = 0;
v___y_1522_ = v___y_1553_;
v___y_1523_ = v_a_1572_;
v___y_1524_ = v___y_1558_;
v___y_1525_ = v___y_1560_;
v___y_1526_ = v___y_1570_;
v___y_1527_ = v___y_1566_;
v___y_1528_ = v___y_1554_;
v___y_1529_ = v___y_1556_;
v___y_1530_ = v___y_1569_;
v___y_1531_ = v___y_1563_;
v___y_1532_ = v___y_1557_;
v___y_1533_ = v___y_1559_;
v___y_1534_ = v___y_1567_;
v___y_1535_ = v___y_1565_;
v___y_1536_ = v___y_1564_;
v___y_1537_ = v_stxForExecution_1562_;
v___y_1538_ = v___y_1568_;
v___y_1539_ = v___y_1561_;
v___y_1540_ = v___x_1573_;
goto v___jp_1521_;
}
else
{
if (v___y_1557_ == 0)
{
lean_object* v_a_1574_; 
v_a_1574_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1571_);
v___y_1522_ = v___y_1553_;
v___y_1523_ = v_a_1574_;
v___y_1524_ = v___y_1558_;
v___y_1525_ = v___y_1560_;
v___y_1526_ = v___y_1570_;
v___y_1527_ = v___y_1566_;
v___y_1528_ = v___y_1554_;
v___y_1529_ = v___y_1556_;
v___y_1530_ = v___y_1569_;
v___y_1531_ = v___y_1563_;
v___y_1532_ = v___y_1557_;
v___y_1533_ = v___y_1559_;
v___y_1534_ = v___y_1567_;
v___y_1535_ = v___y_1565_;
v___y_1536_ = v___y_1564_;
v___y_1537_ = v_stxForExecution_1562_;
v___y_1538_ = v___y_1568_;
v___y_1539_ = v___y_1561_;
v___y_1540_ = v___y_1557_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1575_; lean_object* v_ref_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_a_1575_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1571_);
v_ref_1576_ = lean_ctor_get(v___y_1569_, 4);
v___x_1577_ = 0;
v___x_1578_ = l_Lean_SourceInfo_fromRef(v_ref_1576_, v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1580_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_1579_);
v___x_1581_ = l_Lean_SourceInfo_fromRef(v_tk_1219_, v___x_1203_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1585_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1559_) == 1)
{
lean_object* v_val_1586_; lean_object* v___x_1587_; 
v_val_1586_ = lean_ctor_get(v___y_1559_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v___y_1559_, 1);
v___x_1587_ = l_Array_mkArray1___redArg(v_val_1586_);
v___y_1393_ = v___y_1553_;
v___y_1394_ = v_a_1575_;
v___y_1395_ = v___y_1558_;
v___y_1396_ = v___y_1560_;
v___y_1397_ = v___x_1585_;
v___y_1398_ = v___y_1570_;
v___y_1399_ = v___y_1566_;
v___y_1400_ = v___y_1554_;
v___y_1401_ = v___y_1556_;
v___y_1402_ = v___y_1557_;
v___y_1403_ = v___y_1569_;
v___y_1404_ = v___y_1563_;
v___y_1405_ = v___y_1567_;
v___y_1406_ = v___y_1565_;
v___y_1407_ = v___y_1564_;
v___y_1408_ = v___x_1578_;
v___y_1409_ = v_stxForExecution_1562_;
v___y_1410_ = v___x_1580_;
v___y_1411_ = v___x_1584_;
v___y_1412_ = v___x_1583_;
v___y_1413_ = v___y_1561_;
v___y_1414_ = v___y_1568_;
v___y_1415_ = v___x_1587_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1588_; 
lean_dec(v___y_1559_);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1393_ = v___y_1553_;
v___y_1394_ = v_a_1575_;
v___y_1395_ = v___y_1558_;
v___y_1396_ = v___y_1560_;
v___y_1397_ = v___x_1585_;
v___y_1398_ = v___y_1570_;
v___y_1399_ = v___y_1566_;
v___y_1400_ = v___y_1554_;
v___y_1401_ = v___y_1556_;
v___y_1402_ = v___y_1557_;
v___y_1403_ = v___y_1569_;
v___y_1404_ = v___y_1563_;
v___y_1405_ = v___y_1567_;
v___y_1406_ = v___y_1565_;
v___y_1407_ = v___y_1564_;
v___y_1408_ = v___x_1578_;
v___y_1409_ = v_stxForExecution_1562_;
v___y_1410_ = v___x_1580_;
v___y_1411_ = v___x_1584_;
v___y_1412_ = v___x_1583_;
v___y_1413_ = v___y_1561_;
v___y_1414_ = v___y_1568_;
v___y_1415_ = v___x_1588_;
goto v___jp_1392_;
}
}
}
}
v___jp_1589_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_inc_ref(v___y_1593_);
v___x_1616_ = l_Array_append___redArg(v___y_1593_, v___y_1615_);
lean_dec_ref(v___y_1615_);
lean_inc(v___y_1602_);
lean_inc(v___y_1594_);
v___x_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1594_);
lean_ctor_set(v___x_1617_, 1, v___y_1602_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
lean_inc(v___y_1610_);
v___x_1618_ = l_Lean_Syntax_node6(v___y_1594_, v___y_1599_, v___y_1595_, v___y_1610_, v___y_1601_, v___y_1608_, v___y_1605_, v___x_1617_);
v___y_1553_ = v___y_1590_;
v___y_1554_ = v___y_1609_;
v___y_1555_ = v___y_1610_;
v___y_1556_ = v___y_1611_;
v___y_1557_ = v___y_1596_;
v___y_1558_ = v___y_1603_;
v___y_1559_ = v___y_1597_;
v___y_1560_ = v___y_1604_;
v___y_1561_ = v___y_1614_;
v_stxForExecution_1562_ = v___x_1618_;
v___y_1563_ = v___y_1612_;
v___y_1564_ = v___y_1606_;
v___y_1565_ = v___y_1600_;
v___y_1566_ = v___y_1598_;
v___y_1567_ = v___y_1592_;
v___y_1568_ = v___y_1607_;
v___y_1569_ = v___y_1591_;
v___y_1570_ = v___y_1613_;
goto v___jp_1552_;
}
v___jp_1619_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_inc_ref_n(v___y_1628_, 2);
v___x_1644_ = l_Array_append___redArg(v___y_1628_, v___y_1643_);
lean_dec_ref(v___y_1643_);
lean_inc_n(v___y_1622_, 3);
lean_inc_n(v___y_1631_, 5);
v___x_1645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1631_);
lean_ctor_set(v___x_1645_, 1, v___y_1622_);
lean_ctor_set(v___x_1645_, 2, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1631_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1649_ = l_Lean_Syntax_SepArray_ofElems(v___x_1648_, v___y_1623_);
v___x_1650_ = l_Array_append___redArg(v___y_1628_, v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1631_);
lean_ctor_set(v___x_1651_, 1, v___y_1622_);
lean_ctor_set(v___x_1651_, 2, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1631_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_Syntax_node3(v___y_1631_, v___y_1622_, v___x_1647_, v___x_1651_, v___x_1653_);
if (lean_obj_tag(v___y_1630_) == 1)
{
lean_object* v_val_1655_; lean_object* v___x_1656_; 
v_val_1655_ = lean_ctor_get(v___y_1630_, 0);
lean_inc(v_val_1655_);
v___x_1656_ = l_Array_mkArray1___redArg(v_val_1655_);
v___y_1590_ = v___y_1620_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___y_1626_;
v___y_1593_ = v___y_1628_;
v___y_1594_ = v___y_1631_;
v___y_1595_ = v___y_1634_;
v___y_1596_ = v___y_1635_;
v___y_1597_ = v___y_1636_;
v___y_1598_ = v___y_1638_;
v___y_1599_ = v___y_1640_;
v___y_1600_ = v___y_1642_;
v___y_1601_ = v___y_1621_;
v___y_1602_ = v___y_1622_;
v___y_1603_ = v___y_1623_;
v___y_1604_ = v___y_1624_;
v___y_1605_ = v___x_1654_;
v___y_1606_ = v___y_1627_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___x_1645_;
v___y_1609_ = v___y_1630_;
v___y_1610_ = v___y_1633_;
v___y_1611_ = v___y_1632_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1639_;
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___x_1656_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1590_ = v___y_1620_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___y_1626_;
v___y_1593_ = v___y_1628_;
v___y_1594_ = v___y_1631_;
v___y_1595_ = v___y_1634_;
v___y_1596_ = v___y_1635_;
v___y_1597_ = v___y_1636_;
v___y_1598_ = v___y_1638_;
v___y_1599_ = v___y_1640_;
v___y_1600_ = v___y_1642_;
v___y_1601_ = v___y_1621_;
v___y_1602_ = v___y_1622_;
v___y_1603_ = v___y_1623_;
v___y_1604_ = v___y_1624_;
v___y_1605_ = v___x_1654_;
v___y_1606_ = v___y_1627_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___x_1645_;
v___y_1609_ = v___y_1630_;
v___y_1610_ = v___y_1633_;
v___y_1611_ = v___y_1632_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1639_;
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___x_1657_;
goto v___jp_1589_;
}
}
v___jp_1658_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_inc_ref(v___y_1665_);
v___x_1682_ = l_Array_append___redArg(v___y_1665_, v___y_1681_);
lean_dec_ref(v___y_1681_);
lean_inc(v___y_1660_);
lean_inc(v___y_1668_);
v___x_1683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1668_);
lean_ctor_set(v___x_1683_, 1, v___y_1660_);
lean_ctor_set(v___x_1683_, 2, v___x_1682_);
if (lean_obj_tag(v___y_1662_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_val_1684_ = lean_ctor_get(v___y_1662_, 0);
v___x_1685_ = l_Lean_SourceInfo_fromRef(v_val_1684_, v___x_1203_);
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Array_mkArray1___redArg(v___x_1687_);
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___x_1683_;
v___y_1622_ = v___y_1660_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1662_;
v___y_1625_ = v___y_1663_;
v___y_1626_ = v___y_1664_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1665_;
v___y_1629_ = v___y_1667_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1668_;
v___y_1632_ = v___y_1670_;
v___y_1633_ = v___y_1671_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1672_;
v___y_1636_ = v___y_1674_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1675_;
v___y_1639_ = v___y_1677_;
v___y_1640_ = v___y_1678_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___x_1688_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___x_1683_;
v___y_1622_ = v___y_1660_;
v___y_1623_ = v___y_1661_;
v___y_1624_ = v___y_1662_;
v___y_1625_ = v___y_1663_;
v___y_1626_ = v___y_1664_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1665_;
v___y_1629_ = v___y_1667_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1668_;
v___y_1632_ = v___y_1670_;
v___y_1633_ = v___y_1671_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1672_;
v___y_1636_ = v___y_1674_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1675_;
v___y_1639_ = v___y_1677_;
v___y_1640_ = v___y_1678_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___x_1689_;
goto v___jp_1619_;
}
}
v___jp_1690_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc_ref(v___y_1712_);
v___x_1717_ = l_Array_append___redArg(v___y_1712_, v___y_1716_);
lean_dec_ref(v___y_1716_);
lean_inc(v___y_1711_);
lean_inc(v___y_1696_);
v___x_1718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1718_, 0, v___y_1696_);
lean_ctor_set(v___x_1718_, 1, v___y_1711_);
lean_ctor_set(v___x_1718_, 2, v___x_1717_);
lean_inc(v___y_1709_);
v___x_1719_ = l_Lean_Syntax_node6(v___y_1696_, v___y_1692_, v___y_1698_, v___y_1709_, v___y_1694_, v___y_1704_, v___y_1702_, v___x_1718_);
v___y_1553_ = v___y_1691_;
v___y_1554_ = v___y_1708_;
v___y_1555_ = v___y_1709_;
v___y_1556_ = v___y_1710_;
v___y_1557_ = v___y_1697_;
v___y_1558_ = v___y_1703_;
v___y_1559_ = v___y_1699_;
v___y_1560_ = v___y_1705_;
v___y_1561_ = v___y_1715_;
v_stxForExecution_1562_ = v___x_1719_;
v___y_1563_ = v___y_1713_;
v___y_1564_ = v___y_1706_;
v___y_1565_ = v___y_1701_;
v___y_1566_ = v___y_1700_;
v___y_1567_ = v___y_1695_;
v___y_1568_ = v___y_1707_;
v___y_1569_ = v___y_1693_;
v___y_1570_ = v___y_1714_;
goto v___jp_1552_;
}
v___jp_1720_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_inc_ref_n(v___y_1734_, 2);
v___x_1745_ = l_Array_append___redArg(v___y_1734_, v___y_1744_);
lean_dec_ref(v___y_1744_);
lean_inc_n(v___y_1735_, 3);
lean_inc_n(v___y_1730_, 5);
v___x_1746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1730_);
lean_ctor_set(v___x_1746_, 1, v___y_1735_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1730_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1750_ = l_Lean_Syntax_SepArray_ofElems(v___x_1749_, v___y_1722_);
v___x_1751_ = l_Array_append___redArg(v___y_1734_, v___x_1750_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1752_, 0, v___y_1730_);
lean_ctor_set(v___x_1752_, 1, v___y_1735_);
lean_ctor_set(v___x_1752_, 2, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___y_1730_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node3(v___y_1730_, v___y_1735_, v___x_1748_, v___x_1752_, v___x_1754_);
if (lean_obj_tag(v___y_1731_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1757_; 
v_val_1756_ = lean_ctor_get(v___y_1731_, 0);
lean_inc(v_val_1756_);
v___x_1757_ = l_Array_mkArray1___redArg(v_val_1756_);
v___y_1691_ = v___y_1721_;
v___y_1692_ = v___y_1724_;
v___y_1693_ = v___y_1725_;
v___y_1694_ = v___y_1726_;
v___y_1695_ = v___y_1727_;
v___y_1696_ = v___y_1730_;
v___y_1697_ = v___y_1736_;
v___y_1698_ = v___y_1737_;
v___y_1699_ = v___y_1738_;
v___y_1700_ = v___y_1740_;
v___y_1701_ = v___y_1743_;
v___y_1702_ = v___x_1755_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v___y_1723_;
v___y_1706_ = v___y_1728_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v___y_1731_;
v___y_1709_ = v___y_1733_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1735_;
v___y_1712_ = v___y_1734_;
v___y_1713_ = v___y_1739_;
v___y_1714_ = v___y_1741_;
v___y_1715_ = v___y_1742_;
v___y_1716_ = v___x_1757_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1691_ = v___y_1721_;
v___y_1692_ = v___y_1724_;
v___y_1693_ = v___y_1725_;
v___y_1694_ = v___y_1726_;
v___y_1695_ = v___y_1727_;
v___y_1696_ = v___y_1730_;
v___y_1697_ = v___y_1736_;
v___y_1698_ = v___y_1737_;
v___y_1699_ = v___y_1738_;
v___y_1700_ = v___y_1740_;
v___y_1701_ = v___y_1743_;
v___y_1702_ = v___x_1755_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v___y_1723_;
v___y_1706_ = v___y_1728_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v___y_1731_;
v___y_1709_ = v___y_1733_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1735_;
v___y_1712_ = v___y_1734_;
v___y_1713_ = v___y_1739_;
v___y_1714_ = v___y_1741_;
v___y_1715_ = v___y_1742_;
v___y_1716_ = v___x_1758_;
goto v___jp_1690_;
}
}
v___jp_1759_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_inc_ref(v___y_1773_);
v___x_1783_ = l_Array_append___redArg(v___y_1773_, v___y_1782_);
lean_dec_ref(v___y_1782_);
lean_inc(v___y_1774_);
lean_inc(v___y_1768_);
v___x_1784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1768_);
lean_ctor_set(v___x_1784_, 1, v___y_1774_);
lean_ctor_set(v___x_1784_, 2, v___x_1783_);
if (lean_obj_tag(v___y_1762_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_val_1785_ = lean_ctor_get(v___y_1762_, 0);
v___x_1786_ = l_Lean_SourceInfo_fromRef(v_val_1785_, v___x_1203_);
v___x_1787_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Array_mkArray1___redArg(v___x_1788_);
v___y_1721_ = v___y_1760_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___x_1784_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1766_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
v___y_1731_ = v___y_1769_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1772_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1777_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1780_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___x_1789_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1721_ = v___y_1760_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___x_1784_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1766_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
v___y_1731_ = v___y_1769_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1772_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1777_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1780_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___x_1790_;
goto v___jp_1720_;
}
}
v___jp_1791_:
{
lean_object* v_ref_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_ref_1810_ = lean_ctor_get(v___y_1795_, 4);
v___x_1811_ = l_Lean_SourceInfo_fromRef(v_ref_1810_, v___y_1809_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1206_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v___x_1204_);
v___x_1813_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_1812_);
v___x_1814_ = l_Lean_SourceInfo_fromRef(v_tk_1219_, v___x_1203_);
v___x_1815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1812_);
v___x_1816_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1817_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1803_) == 1)
{
lean_object* v_val_1818_; lean_object* v___x_1819_; 
v_val_1818_ = lean_ctor_get(v___y_1803_, 0);
lean_inc(v_val_1818_);
v___x_1819_ = l_Array_mkArray1___redArg(v_val_1818_);
v___y_1760_ = v___y_1792_;
v___y_1761_ = v___y_1793_;
v___y_1762_ = v___y_1794_;
v___y_1763_ = v___x_1813_;
v___y_1764_ = v___y_1795_;
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___x_1811_;
v___y_1769_ = v___y_1799_;
v___y_1770_ = v___y_1800_;
v___y_1771_ = v___y_1801_;
v___y_1772_ = v___y_1802_;
v___y_1773_ = v___x_1817_;
v___y_1774_ = v___x_1816_;
v___y_1775_ = v___x_1815_;
v___y_1776_ = v___y_1803_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1807_;
v___y_1781_ = v___y_1808_;
v___y_1782_ = v___x_1819_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1760_ = v___y_1792_;
v___y_1761_ = v___y_1793_;
v___y_1762_ = v___y_1794_;
v___y_1763_ = v___x_1813_;
v___y_1764_ = v___y_1795_;
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___x_1811_;
v___y_1769_ = v___y_1799_;
v___y_1770_ = v___y_1800_;
v___y_1771_ = v___y_1801_;
v___y_1772_ = v___y_1802_;
v___y_1773_ = v___x_1817_;
v___y_1774_ = v___x_1816_;
v___y_1775_ = v___x_1815_;
v___y_1776_ = v___y_1803_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1807_;
v___y_1781_ = v___y_1808_;
v___y_1782_ = v___x_1820_;
goto v___jp_1759_;
}
}
v___jp_1821_:
{
if (lean_obj_tag(v___y_1829_) == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = 0;
v___y_1792_ = v___y_1822_;
v___y_1793_ = v_argsArray_1830_;
v___y_1794_ = v___y_1827_;
v___y_1795_ = v___y_1837_;
v___y_1796_ = v___y_1835_;
v___y_1797_ = v___y_1832_;
v___y_1798_ = v___y_1836_;
v___y_1799_ = v___y_1823_;
v___y_1800_ = v___y_1824_;
v___y_1801_ = v___y_1825_;
v___y_1802_ = v___y_1826_;
v___y_1803_ = v___y_1828_;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1831_;
v___y_1806_ = v___y_1838_;
v___y_1807_ = v___y_1829_;
v___y_1808_ = v___y_1833_;
v___y_1809_ = v___x_1839_;
goto v___jp_1791_;
}
else
{
if (v___y_1826_ == 0)
{
v___y_1792_ = v___y_1822_;
v___y_1793_ = v_argsArray_1830_;
v___y_1794_ = v___y_1827_;
v___y_1795_ = v___y_1837_;
v___y_1796_ = v___y_1835_;
v___y_1797_ = v___y_1832_;
v___y_1798_ = v___y_1836_;
v___y_1799_ = v___y_1823_;
v___y_1800_ = v___y_1824_;
v___y_1801_ = v___y_1825_;
v___y_1802_ = v___y_1826_;
v___y_1803_ = v___y_1828_;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1831_;
v___y_1806_ = v___y_1838_;
v___y_1807_ = v___y_1829_;
v___y_1808_ = v___y_1833_;
v___y_1809_ = v___y_1826_;
goto v___jp_1791_;
}
else
{
lean_object* v_ref_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_ref_1840_ = lean_ctor_get(v___y_1837_, 4);
v___x_1841_ = 0;
v___x_1842_ = l_Lean_SourceInfo_fromRef(v_ref_1840_, v___x_1841_);
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1206_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v___x_1204_);
v___x_1844_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_1843_);
v___x_1845_ = l_Lean_SourceInfo_fromRef(v_tk_1219_, v___x_1203_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1849_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1828_) == 1)
{
lean_object* v_val_1850_; lean_object* v___x_1851_; 
v_val_1850_ = lean_ctor_get(v___y_1828_, 0);
lean_inc(v_val_1850_);
v___x_1851_ = l_Array_mkArray1___redArg(v_val_1850_);
v___y_1659_ = v___y_1822_;
v___y_1660_ = v___x_1848_;
v___y_1661_ = v_argsArray_1830_;
v___y_1662_ = v___y_1827_;
v___y_1663_ = v___y_1837_;
v___y_1664_ = v___y_1835_;
v___y_1665_ = v___x_1849_;
v___y_1666_ = v___y_1832_;
v___y_1667_ = v___y_1836_;
v___y_1668_ = v___x_1842_;
v___y_1669_ = v___y_1823_;
v___y_1670_ = v___y_1824_;
v___y_1671_ = v___y_1825_;
v___y_1672_ = v___y_1826_;
v___y_1673_ = v___x_1847_;
v___y_1674_ = v___y_1828_;
v___y_1675_ = v___y_1834_;
v___y_1676_ = v___y_1831_;
v___y_1677_ = v___y_1838_;
v___y_1678_ = v___x_1844_;
v___y_1679_ = v___y_1829_;
v___y_1680_ = v___y_1833_;
v___y_1681_ = v___x_1851_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1659_ = v___y_1822_;
v___y_1660_ = v___x_1848_;
v___y_1661_ = v_argsArray_1830_;
v___y_1662_ = v___y_1827_;
v___y_1663_ = v___y_1837_;
v___y_1664_ = v___y_1835_;
v___y_1665_ = v___x_1849_;
v___y_1666_ = v___y_1832_;
v___y_1667_ = v___y_1836_;
v___y_1668_ = v___x_1842_;
v___y_1669_ = v___y_1823_;
v___y_1670_ = v___y_1824_;
v___y_1671_ = v___y_1825_;
v___y_1672_ = v___y_1826_;
v___y_1673_ = v___x_1847_;
v___y_1674_ = v___y_1828_;
v___y_1675_ = v___y_1834_;
v___y_1676_ = v___y_1831_;
v___y_1677_ = v___y_1838_;
v___y_1678_ = v___x_1844_;
v___y_1679_ = v___y_1829_;
v___y_1680_ = v___y_1833_;
v___y_1681_ = v___x_1852_;
goto v___jp_1658_;
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1859_, v___y_1868_, v___y_1858_, v___y_1865_, v___y_1855_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_Lean_LibrarySuggestions_select(v_a_1873_, v___y_1871_, v___y_1868_, v___y_1858_, v___y_1865_, v___y_1855_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v_sz_1876_ = lean_array_size(v_a_1875_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1875_, v_sz_1876_, v___x_1877_, v___y_1866_, v___y_1869_, v___y_1859_, v___y_1864_, v___y_1857_, v___y_1868_, v___y_1858_, v___y_1865_, v___y_1855_);
lean_dec(v_a_1875_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___y_1822_ = v___y_1854_;
v___y_1823_ = v___y_1860_;
v___y_1824_ = v___y_1861_;
v___y_1825_ = v___y_1862_;
v___y_1826_ = v___y_1863_;
v___y_1827_ = v___y_1856_;
v___y_1828_ = v___y_1867_;
v___y_1829_ = v___y_1870_;
v_argsArray_1830_ = v_a_1879_;
v___y_1831_ = v___y_1869_;
v___y_1832_ = v___y_1859_;
v___y_1833_ = v___y_1864_;
v___y_1834_ = v___y_1857_;
v___y_1835_ = v___y_1868_;
v___y_1836_ = v___y_1858_;
v___y_1837_ = v___y_1865_;
v___y_1838_ = v___y_1855_;
goto v___jp_1821_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v___y_1870_);
lean_dec(v___y_1867_);
lean_dec(v___y_1862_);
lean_dec(v___y_1860_);
lean_dec(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v_a_1880_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1878_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v___y_1870_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1862_);
lean_dec(v___y_1860_);
lean_dec(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v_a_1888_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1874_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1874_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1862_);
lean_dec(v___y_1860_);
lean_dec(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v_a_1896_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1872_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1872_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
v___jp_1904_:
{
lean_object* v_config_1923_; uint8_t v_suggestions_1924_; 
v_config_1923_ = lean_ctor_get(v___y_1920_, 0);
lean_inc_ref(v_config_1923_);
lean_dec_ref(v___y_1920_);
v_suggestions_1924_ = lean_ctor_get_uint8(v_config_1923_, sizeof(void*)*3 + 26);
if (v_suggestions_1924_ == 0)
{
lean_dec_ref(v_config_1923_);
lean_dec_ref(v___f_1207_);
v___y_1822_ = v___y_1905_;
v___y_1823_ = v___y_1911_;
v___y_1824_ = v___y_1912_;
v___y_1825_ = v___y_1913_;
v___y_1826_ = v___y_1914_;
v___y_1827_ = v___y_1907_;
v___y_1828_ = v___y_1918_;
v___y_1829_ = v___y_1921_;
v_argsArray_1830_ = v___y_1922_;
v___y_1831_ = v___y_1919_;
v___y_1832_ = v___y_1910_;
v___y_1833_ = v___y_1915_;
v___y_1834_ = v___y_1908_;
v___y_1835_ = v___y_1917_;
v___y_1836_ = v___y_1909_;
v___y_1837_ = v___y_1916_;
v___y_1838_ = v___y_1906_;
goto v___jp_1821_;
}
else
{
lean_object* v_maxSuggestions_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_maxSuggestions_1925_ = lean_ctor_get(v_config_1923_, 2);
lean_inc(v_maxSuggestions_1925_);
lean_dec_ref(v_config_1923_);
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1927_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1925_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_unsigned_to_nat(100u);
v___x_1929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1926_);
lean_ctor_set(v___x_1929_, 2, v___f_1207_);
lean_ctor_set(v___x_1929_, 3, v___x_1927_);
v___y_1854_ = v___y_1905_;
v___y_1855_ = v___y_1906_;
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1911_;
v___y_1861_ = v___y_1912_;
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1914_;
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1922_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1917_;
v___y_1869_ = v___y_1919_;
v___y_1870_ = v___y_1921_;
v___y_1871_ = v___x_1929_;
goto v___jp_1853_;
}
else
{
lean_object* v_val_1930_; lean_object* v___x_1931_; 
v_val_1930_ = lean_ctor_get(v_maxSuggestions_1925_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v_maxSuggestions_1925_, 1);
v___x_1931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1931_, 0, v_val_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1926_);
lean_ctor_set(v___x_1931_, 2, v___f_1207_);
lean_ctor_set(v___x_1931_, 3, v___x_1927_);
v___y_1854_ = v___y_1905_;
v___y_1855_ = v___y_1906_;
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1911_;
v___y_1861_ = v___y_1912_;
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1914_;
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1922_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1917_;
v___y_1869_ = v___y_1919_;
v___y_1870_ = v___y_1921_;
v___y_1871_ = v___x_1931_;
goto v___jp_1853_;
}
}
}
v___jp_1932_:
{
uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = 0;
lean_inc(v___y_1944_);
v___x_1949_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1944_, v___x_1948_, v___y_1933_, v___y_1934_, v___y_1946_);
if (lean_obj_tag(v___x_1949_) == 0)
{
if (lean_obj_tag(v___y_1940_) == 1)
{
lean_object* v_a_1950_; lean_object* v_val_1951_; lean_object* v___x_1952_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v_val_1951_ = lean_ctor_get(v___y_1940_, 0);
lean_inc(v_val_1951_);
lean_dec_ref_known(v___y_1940_, 1);
v___x_1952_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1951_);
lean_dec(v_val_1951_);
lean_inc(v___y_1942_);
v___y_1905_ = v___y_1942_;
v___y_1906_ = v___y_1946_;
v___y_1907_ = v___y_1941_;
v___y_1908_ = v___y_1936_;
v___y_1909_ = v___y_1938_;
v___y_1910_ = v___y_1945_;
v___y_1911_ = v___y_1942_;
v___y_1912_ = v___x_1948_;
v___y_1913_ = v___y_1944_;
v___y_1914_ = v___y_1937_;
v___y_1915_ = v___y_1943_;
v___y_1916_ = v___y_1934_;
v___y_1917_ = v___y_1939_;
v___y_1918_ = v___y_1947_;
v___y_1919_ = v___y_1933_;
v___y_1920_ = v_a_1950_;
v___y_1921_ = v___y_1935_;
v___y_1922_ = v___x_1952_;
goto v___jp_1904_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
lean_dec(v___y_1940_);
v_a_1953_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1942_);
v___y_1905_ = v___y_1942_;
v___y_1906_ = v___y_1946_;
v___y_1907_ = v___y_1941_;
v___y_1908_ = v___y_1936_;
v___y_1909_ = v___y_1938_;
v___y_1910_ = v___y_1945_;
v___y_1911_ = v___y_1942_;
v___y_1912_ = v___x_1948_;
v___y_1913_ = v___y_1944_;
v___y_1914_ = v___y_1937_;
v___y_1915_ = v___y_1943_;
v___y_1916_ = v___y_1934_;
v___y_1917_ = v___y_1939_;
v___y_1918_ = v___y_1947_;
v___y_1919_ = v___y_1933_;
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___y_1935_;
v___y_1922_ = v___x_1954_;
goto v___jp_1904_;
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___y_1947_);
lean_dec(v___y_1944_);
lean_dec(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v___y_1935_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v_a_1955_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1949_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1949_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
v___jp_1963_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Syntax_getOptional_x3f(v___y_1964_);
lean_dec(v___y_1964_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_box(0);
v___y_1933_ = v___y_1975_;
v___y_1934_ = v___y_1973_;
v___y_1935_ = v___y_1976_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1971_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1974_;
v___y_1940_ = v___y_1977_;
v___y_1941_ = v___y_1966_;
v___y_1942_ = v___y_1978_;
v___y_1943_ = v___y_1972_;
v___y_1944_ = v___y_1970_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1965_;
v___y_1947_ = v___x_1980_;
goto v___jp_1932_;
}
else
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_val_1981_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v___y_1933_ = v___y_1975_;
v___y_1934_ = v___y_1973_;
v___y_1935_ = v___y_1976_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1971_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1974_;
v___y_1940_ = v___y_1977_;
v___y_1941_ = v___y_1966_;
v___y_1942_ = v___y_1978_;
v___y_1943_ = v___y_1972_;
v___y_1944_ = v___y_1970_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1965_;
v___y_1947_ = v___x_1986_;
goto v___jp_1932_;
}
}
}
}
v___jp_1989_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_unsigned_to_nat(4u);
v___x_2006_ = l_Lean_Syntax_getArg(v___y_1994_, v___x_2005_);
lean_dec(v___y_1994_);
v___x_2007_ = l_Lean_Syntax_getOptional_x3f(v___x_2006_);
lean_dec(v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_2004_;
v___y_1966_ = v___y_1993_;
v___y_1967_ = v___y_2000_;
v___y_1968_ = v___y_2002_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1991_;
v___y_1972_ = v___y_1999_;
v___y_1973_ = v___y_2003_;
v___y_1974_ = v___y_2001_;
v___y_1975_ = v___y_1997_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v_args_1996_;
v___y_1978_ = v___x_2008_;
goto v___jp_1963_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2007_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_val_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_2004_;
v___y_1966_ = v___y_1993_;
v___y_1967_ = v___y_2000_;
v___y_1968_ = v___y_2002_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1991_;
v___y_1972_ = v___y_1999_;
v___y_1973_ = v___y_2003_;
v___y_1974_ = v___y_2001_;
v___y_1975_ = v___y_1997_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v_args_1996_;
v___y_1978_ = v___x_2014_;
goto v___jp_1963_;
}
}
}
}
v___jp_2018_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_unsigned_to_nat(3u);
v___x_2034_ = l_Lean_Syntax_getArg(v___y_2022_, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_isNone(v___x_2034_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; 
lean_inc(v___x_2034_);
v___x_2036_ = l_Lean_Syntax_matchesNull(v___x_2034_, v___x_2017_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; 
lean_dec(v___x_2034_);
lean_dec(v_o_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2037_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2038_ = l_Lean_Syntax_getArg(v___x_2034_, v___x_1218_);
lean_dec(v___x_2034_);
v___x_2039_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1206_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v___x_1204_);
v___x_2040_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_2039_);
lean_inc(v___x_2038_);
v___x_2041_ = l_Lean_Syntax_isOfKind(v___x_2038_, v___x_2040_);
lean_dec(v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec(v___x_2038_);
lean_dec(v_o_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v_args_2044_; lean_object* v___x_2045_; 
v___x_2043_ = l_Lean_Syntax_getArg(v___x_2038_, v___x_2017_);
lean_dec(v___x_2038_);
v_args_2044_ = l_Lean_Syntax_getArgs(v___x_2043_);
lean_dec(v___x_2043_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_args_2044_);
v___y_1990_ = v___y_2019_;
v___y_1991_ = v___y_2020_;
v___y_1992_ = v___y_2021_;
v___y_1993_ = v_o_2024_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___y_2023_;
v_args_1996_ = v___x_2045_;
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___y_2027_;
v___y_2000_ = v___y_2028_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v___x_2046_; 
lean_dec(v___x_2034_);
v___x_2046_ = lean_box(0);
v___y_1990_ = v___y_2019_;
v___y_1991_ = v___y_2020_;
v___y_1992_ = v___y_2021_;
v___y_1993_ = v_o_2024_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___y_2023_;
v_args_1996_ = v___x_2046_;
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___y_2027_;
v___y_2000_ = v___y_2028_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
goto v___jp_1989_;
}
}
v___jp_2047_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2057_ = lean_unsigned_to_nat(2u);
v___x_2058_ = l_Lean_Syntax_getArg(v_stx_1202_, v___x_2057_);
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1206_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v___x_1204_);
v___x_2060_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_2059_);
lean_inc(v___x_2058_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v___x_2058_, v___x_2060_);
lean_dec(v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v___x_2058_);
lean_dec(v_bang_2048_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2062_;
}
else
{
lean_object* v_cfg_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v_cfg_2063_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_1218_);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1206_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v___x_1204_);
v___x_2065_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_2064_);
lean_inc(v_cfg_2063_);
v___x_2066_ = l_Lean_Syntax_isOfKind(v_cfg_2063_, v___x_2065_);
lean_dec(v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v_cfg_2063_);
lean_dec(v___x_2058_);
lean_dec(v_bang_2048_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2067_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_2017_);
v___x_2069_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_2057_);
v___x_2070_ = l_Lean_Syntax_isNone(v___x_2069_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; 
lean_inc(v___x_2069_);
v___x_2071_ = l_Lean_Syntax_matchesNull(v___x_2069_, v___x_2017_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v___x_2069_);
lean_dec(v___x_2068_);
lean_dec(v_cfg_2063_);
lean_dec(v___x_2058_);
lean_dec(v_bang_2048_);
lean_dec(v_tk_1219_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v___x_2072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2072_;
}
else
{
lean_object* v_o_2073_; lean_object* v___x_2074_; 
v_o_2073_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_1218_);
lean_dec(v___x_2069_);
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_o_2073_);
v___y_2019_ = v_cfg_2063_;
v___y_2020_ = v___x_2061_;
v___y_2021_ = v___x_2068_;
v___y_2022_ = v___x_2058_;
v___y_2023_ = v_bang_2048_;
v_o_2024_ = v___x_2074_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2050_;
v___y_2027_ = v___y_2051_;
v___y_2028_ = v___y_2052_;
v___y_2029_ = v___y_2053_;
v___y_2030_ = v___y_2054_;
v___y_2031_ = v___y_2055_;
v___y_2032_ = v___y_2056_;
goto v___jp_2018_;
}
}
else
{
lean_object* v___x_2075_; 
lean_dec(v___x_2069_);
v___x_2075_ = lean_box(0);
v___y_2019_ = v_cfg_2063_;
v___y_2020_ = v___x_2061_;
v___y_2021_ = v___x_2068_;
v___y_2022_ = v___x_2058_;
v___y_2023_ = v_bang_2048_;
v_o_2024_ = v___x_2075_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2050_;
v___y_2027_ = v___y_2051_;
v___y_2028_ = v___y_2052_;
v___y_2029_ = v___y_2053_;
v___y_2030_ = v___y_2054_;
v___y_2031_ = v___y_2055_;
v___y_2032_ = v___y_2056_;
goto v___jp_2018_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2083_, lean_object* v_stx_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v___f_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_35404__boxed_2099_; uint8_t v___x_35405__boxed_2100_; lean_object* v_res_2101_; 
v___x_35404__boxed_2099_ = lean_unbox(v___x_2083_);
v___x_35405__boxed_2100_ = lean_unbox(v___x_2085_);
v_res_2101_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35404__boxed_2099_, v_stx_2084_, v___x_35405__boxed_2100_, v___x_2086_, v___x_2087_, v___x_2088_, v___f_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v_stx_2084_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; uint8_t v___x_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___y_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2111_);
v___x_2125_ = l_Lean_Syntax_isOfKind(v_stx_2111_, v___x_2124_);
v___x_2126_ = 1;
v___f_2127_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2128_ = lean_box(v___x_2125_);
v___x_2129_ = lean_box(v___x_2126_);
v___y_2130_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2130_, 0, v___x_2128_);
lean_closure_set(v___y_2130_, 1, v_stx_2111_);
lean_closure_set(v___y_2130_, 2, v___x_2129_);
lean_closure_set(v___y_2130_, 3, v___x_2121_);
lean_closure_set(v___y_2130_, 4, v___x_2122_);
lean_closure_set(v___y_2130_, 5, v___x_2123_);
lean_closure_set(v___y_2130_, 6, v___f_2127_);
v___x_2131_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2131_, 0, v___y_2130_);
v___x_2132_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2131_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2144_, lean_object* v_as_2145_, lean_object* v_as_x27_2146_, lean_object* v_b_2147_, lean_object* v_a_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2144_, v_as_x27_2146_, v_b_2147_, v___y_2155_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2159_, lean_object* v_as_2160_, lean_object* v_as_x27_2161_, lean_object* v_b_2162_, lean_object* v_a_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2159_, v_as_2160_, v_as_x27_2161_, v_b_2162_, v_a_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_as_x27_2161_);
lean_dec(v_as_2160_);
lean_dec(v___x_2159_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2174_, lean_object* v_ref_2175_, lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2175_, v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2187_, lean_object* v_ref_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2187_, v_ref_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v_ref_2188_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2200_, lean_object* v_ref_2201_, lean_object* v_constName_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2201_, v_constName_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2213_, lean_object* v_ref_2214_, lean_object* v_constName_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2213_, v_ref_2214_, v_constName_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_ref_2214_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2226_, lean_object* v_msg_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2227_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2238_, v_msg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2250_, v___y_2257_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_opt_2261_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2272_, lean_object* v_ref_2273_, lean_object* v_msg_2274_, lean_object* v_declHint_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2273_, v_msg_2274_, v_declHint_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_ref_2287_, lean_object* v_msg_2288_, lean_object* v_declHint_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2286_, v_ref_2287_, v_msg_2288_, v_declHint_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v_ref_2287_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2300_, v_declHint_2301_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2312_, lean_object* v_declHint_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2312_, v_declHint_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2324_, lean_object* v_msgData_2325_, uint8_t v_severity_2326_, uint8_t v_isSilent_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2324_, v_msgData_2325_, v_severity_2326_, v_isSilent_2327_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2338_, lean_object* v_msgData_2339_, lean_object* v_severity_2340_, lean_object* v_isSilent_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_severity_boxed_2351_; uint8_t v_isSilent_boxed_2352_; lean_object* v_res_2353_; 
v_severity_boxed_2351_ = lean_unbox(v_severity_2340_);
v_isSilent_boxed_2352_ = lean_unbox(v_isSilent_2341_);
v_res_2353_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2338_, v_msgData_2339_, v_severity_boxed_2351_, v_isSilent_boxed_2352_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v_ref_2338_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2361_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2362_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2364_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2365_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2361_, v___x_2362_, v___x_2363_, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2396_ = l_Lean_addBuiltinDeclarationRanges(v___x_2394_, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2399_, lean_object* v_as_x27_2400_, lean_object* v_b_2401_, lean_object* v___y_2402_){
_start:
{
if (lean_obj_tag(v_as_x27_2400_) == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_b_2401_);
return v___x_2404_;
}
else
{
lean_object* v_head_2405_; lean_object* v_tail_2406_; lean_object* v_ref_2407_; uint8_t v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_head_2405_ = lean_ctor_get(v_as_x27_2400_, 0);
v_tail_2406_ = lean_ctor_get(v_as_x27_2400_, 1);
v_ref_2407_ = lean_ctor_get(v___y_2402_, 4);
v___x_2408_ = 1;
v___x_2409_ = 0;
v___x_2410_ = l_Lean_SourceInfo_fromRef(v_ref_2407_, v___x_2409_);
v___x_2411_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2412_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2413_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2410_);
v___x_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2410_);
lean_ctor_set(v___x_2414_, 1, v___x_2412_);
lean_ctor_set(v___x_2414_, 2, v___x_2413_);
lean_inc(v_head_2405_);
v___x_2415_ = l_Lean_mkCIdentFrom(v___x_2399_, v_head_2405_, v___x_2408_);
lean_inc_ref(v___x_2414_);
v___x_2416_ = l_Lean_Syntax_node3(v___x_2410_, v___x_2411_, v___x_2414_, v___x_2414_, v___x_2415_);
v___x_2417_ = lean_array_push(v_b_2401_, v___x_2416_);
v_as_x27_2400_ = v_tail_2406_;
v_b_2401_ = v___x_2417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2419_, lean_object* v_as_x27_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2419_, v_as_x27_2420_, v_b_2421_, v___y_2422_);
lean_dec_ref(v___y_2422_);
lean_dec(v_as_x27_2420_);
lean_dec(v___x_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2425_, size_t v_sz_2426_, size_t v_i_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_lt(v_i_2427_, v_sz_2426_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_b_2428_);
return v___x_2439_;
}
else
{
lean_object* v_a_2440_; lean_object* v_name_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_a_2440_ = lean_array_uget_borrowed(v_as_2425_, v_i_2427_);
v_name_2441_ = lean_ctor_get(v_a_2440_, 0);
lean_inc(v_name_2441_);
v___x_2442_ = l_Lean_mkIdent(v_name_2441_);
lean_inc(v___x_2442_);
v___x_2443_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2442_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2442_, v_a_2444_, v_b_2428_, v___y_2435_);
lean_dec(v_a_2444_);
lean_dec(v___x_2442_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; size_t v___x_2447_; size_t v___x_2448_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_add(v_i_2427_, v___x_2447_);
v_i_2427_ = v___x_2448_;
v_b_2428_ = v_a_2446_;
goto _start;
}
else
{
return v___x_2445_;
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v___x_2442_);
lean_dec_ref(v_b_2428_);
v_a_2450_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2443_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2443_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2458_, lean_object* v_sz_2459_, lean_object* v_i_2460_, lean_object* v_b_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
size_t v_sz_boxed_2471_; size_t v_i_boxed_2472_; lean_object* v_res_2473_; 
v_sz_boxed_2471_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2472_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2458_, v_sz_boxed_2471_, v_i_boxed_2472_, v_b_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_as_2458_);
return v_res_2473_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2477_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_unsigned_to_nat(32u);
v___x_2481_ = lean_mk_empty_array_with_capacity(v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = ((size_t)5ULL);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_unsigned_to_nat(32u);
v___x_2486_ = lean_mk_empty_array_with_capacity(v___x_2485_);
v___x_2487_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2486_);
lean_ctor_set(v___x_2488_, 2, v___x_2484_);
lean_ctor_set(v___x_2488_, 3, v___x_2484_);
lean_ctor_set_usize(v___x_2488_, 4, v___x_2483_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2490_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
lean_ctor_set(v___x_2491_, 2, v___x_2490_);
lean_ctor_set(v___x_2491_, 3, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2493_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2503_, lean_object* v_stx_2504_, uint8_t v___x_2505_, lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v___f_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
if (v___x_2503_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_2519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; lean_object* v_tk_2521_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2636_; uint8_t v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2639_; lean_object* v_stxForSuggestion_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; uint8_t v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; uint8_t v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; uint8_t v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; uint8_t v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; uint8_t v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; uint8_t v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; uint8_t v___y_2939_; uint8_t v___y_2940_; lean_object* v_stxForExecution_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; uint8_t v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; uint8_t v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; uint8_t v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; uint8_t v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; uint8_t v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; uint8_t v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; uint8_t v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; uint8_t v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; uint8_t v___y_3270_; uint8_t v___y_3271_; lean_object* v_argsArray_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v_args_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___x_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v_o_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v_bang_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v_tk_2521_ = l_Lean_Syntax_getArg(v_stx_2504_, v___x_2520_);
v___x_3451_ = lean_unsigned_to_nat(1u);
v___x_3510_ = l_Lean_Syntax_getArg(v_stx_2504_, v___x_3451_);
v___x_3511_ = l_Lean_Syntax_isNone(v___x_3510_);
if (v___x_3511_ == 0)
{
uint8_t v___x_3512_; 
lean_inc(v___x_3510_);
v___x_3512_ = l_Lean_Syntax_matchesNull(v___x_3510_, v___x_3451_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec(v___x_3510_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3513_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3513_;
}
else
{
lean_object* v_bang_3514_; lean_object* v___x_3515_; 
v_bang_3514_ = l_Lean_Syntax_getArg(v___x_3510_, v___x_2520_);
lean_dec(v___x_3510_);
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v_bang_3514_);
v_bang_3482_ = v___x_3515_;
v___y_3483_ = v___y_2510_;
v___y_3484_ = v___y_2511_;
v___y_3485_ = v___y_2512_;
v___y_3486_ = v___y_2513_;
v___y_3487_ = v___y_2514_;
v___y_3488_ = v___y_2515_;
v___y_3489_ = v___y_2516_;
v___y_3490_ = v___y_2517_;
goto v___jp_3481_;
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v___x_3510_);
v___x_3516_ = lean_box(0);
v_bang_3482_ = v___x_3516_;
v___y_3483_ = v___y_2510_;
v___y_3484_ = v___y_2511_;
v___y_3485_ = v___y_2512_;
v___y_3486_ = v___y_2513_;
v___y_3487_ = v___y_2514_;
v___y_3488_ = v___y_2515_;
v___y_3489_ = v___y_2516_;
v___y_3490_ = v___y_2517_;
goto v___jp_3481_;
}
v___jp_2522_:
{
lean_object* v_usedTheorems_2529_; lean_object* v_diag_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2572_; 
v_usedTheorems_2529_ = lean_ctor_get(v___y_2523_, 0);
v_diag_2530_ = lean_ctor_get(v___y_2523_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___y_2523_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2532_ = v___y_2523_;
v_isShared_2533_ = v_isSharedCheck_2572_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_diag_2530_);
lean_inc(v_usedTheorems_2529_);
lean_dec(v___y_2523_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2572_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2524_, v_usedTheorems_2529_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec_ref(v_usedTheorems_2529_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v_ref_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v_ref_2536_ = lean_ctor_get(v___y_2527_, 4);
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 1, v_a_2535_);
lean_ctor_set(v___x_2532_, 0, v___x_2537_);
v___x_2539_ = v___x_2532_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_a_2535_);
v___x_2539_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v___x_2540_);
lean_ctor_set(v___x_2541_, 5, v___x_2540_);
lean_inc(v_ref_2536_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_ref_2536_);
v___x_2543_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2544_ = 4;
v___x_2545_ = l_Lean_MessageData_nil;
v___x_2546_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2521_, v___x_2541_, v___x_2542_, v___x_2543_, v___x_2540_, v___x_2544_, v___x_2545_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2554_);
v___x_2548_ = v___x_2546_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v___x_2546_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_diag_2530_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_diag_2530_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_diag_2530_);
v_a_2555_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2546_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2546_);
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
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_del_object(v___x_2532_);
lean_dec_ref(v_diag_2530_);
lean_dec(v_tk_2521_);
v_a_2564_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2534_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2534_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2580_, v___y_2575_, v___y_2576_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2585_ = l_Lean_Meta_simpAll(v_a_2583_, v___y_2581_, v___y_2577_, v___x_2584_, v___y_2575_, v___y_2576_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v_fst_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v_fst_2587_ = lean_ctor_get(v_a_2586_, 0);
if (lean_obj_tag(v_fst_2587_) == 0)
{
lean_object* v_snd_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_snd_2588_ = lean_ctor_get(v_a_2586_, 1);
lean_inc(v_snd_2588_);
lean_dec(v_a_2586_);
v___x_2589_ = lean_box(0);
v___x_2590_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2589_, v___y_2580_, v___y_2575_, v___y_2576_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_dec_ref_known(v___x_2590_, 1);
v___y_2523_ = v_snd_2588_;
v___y_2524_ = v___y_2574_;
v___y_2525_ = v___y_2575_;
v___y_2526_ = v___y_2576_;
v___y_2527_ = v___y_2578_;
v___y_2528_ = v___y_2579_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_snd_2588_);
lean_dec(v___y_2574_);
lean_dec(v_tk_2521_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_snd_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2617_; 
lean_inc_ref(v_fst_2587_);
v_snd_2599_ = lean_ctor_get(v_a_2586_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2586_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v_a_2586_, 0);
lean_dec(v_unused_2618_);
v___x_2601_ = v_a_2586_;
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_snd_2599_);
lean_dec(v_a_2586_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_val_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v_val_2603_ = lean_ctor_get(v_fst_2587_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v_fst_2587_, 1);
v___x_2604_ = lean_box(0);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 1);
lean_ctor_set(v___x_2601_, 1, v___x_2604_);
lean_ctor_set(v___x_2601_, 0, v_val_2603_);
v___x_2606_ = v___x_2601_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_val_2603_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2606_, v___y_2580_, v___y_2575_, v___y_2576_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_dec_ref_known(v___x_2607_, 1);
v___y_2523_ = v_snd_2599_;
v___y_2524_ = v___y_2574_;
v___y_2525_ = v___y_2575_;
v___y_2526_ = v___y_2576_;
v___y_2527_ = v___y_2578_;
v___y_2528_ = v___y_2579_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_snd_2599_);
lean_dec(v___y_2574_);
lean_dec(v_tk_2521_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v___y_2574_);
lean_dec(v_tk_2521_);
v_a_2619_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2585_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2585_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2574_);
lean_dec(v_tk_2521_);
v_a_2627_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2582_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2582_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2650_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2639_, v___x_2505_, v___y_2638_, v___x_2505_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2639_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
if (lean_obj_tag(v___y_2636_) == 0)
{
lean_object* v_ctx_2652_; lean_object* v_simprocs_2653_; 
v_ctx_2652_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_ctx_2652_);
v_simprocs_2653_ = lean_ctor_get(v_a_2651_, 1);
lean_inc_ref(v_simprocs_2653_);
lean_dec(v_a_2651_);
v___y_2574_ = v_stxForSuggestion_2640_;
v___y_2575_ = v___y_2645_;
v___y_2576_ = v___y_2646_;
v___y_2577_ = v_simprocs_2653_;
v___y_2578_ = v___y_2647_;
v___y_2579_ = v___y_2648_;
v___y_2580_ = v___y_2642_;
v___y_2581_ = v_ctx_2652_;
goto v___jp_2573_;
}
else
{
lean_dec_ref_known(v___y_2636_, 1);
if (v___y_2637_ == 0)
{
lean_object* v_ctx_2654_; lean_object* v_simprocs_2655_; 
v_ctx_2654_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_ctx_2654_);
v_simprocs_2655_ = lean_ctor_get(v_a_2651_, 1);
lean_inc_ref(v_simprocs_2655_);
lean_dec(v_a_2651_);
v___y_2574_ = v_stxForSuggestion_2640_;
v___y_2575_ = v___y_2645_;
v___y_2576_ = v___y_2646_;
v___y_2577_ = v_simprocs_2655_;
v___y_2578_ = v___y_2647_;
v___y_2579_ = v___y_2648_;
v___y_2580_ = v___y_2642_;
v___y_2581_ = v_ctx_2654_;
goto v___jp_2573_;
}
else
{
lean_object* v_ctx_2656_; lean_object* v_simprocs_2657_; lean_object* v___x_2658_; 
v_ctx_2656_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_ctx_2656_);
v_simprocs_2657_ = lean_ctor_get(v_a_2651_, 1);
lean_inc_ref(v_simprocs_2657_);
lean_dec(v_a_2651_);
v___x_2658_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2656_);
v___y_2574_ = v_stxForSuggestion_2640_;
v___y_2575_ = v___y_2645_;
v___y_2576_ = v___y_2646_;
v___y_2577_ = v_simprocs_2657_;
v___y_2578_ = v___y_2647_;
v___y_2579_ = v___y_2648_;
v___y_2580_ = v___y_2642_;
v___y_2581_ = v___x_2658_;
goto v___jp_2573_;
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_stxForSuggestion_2640_);
lean_dec(v___y_2636_);
lean_dec(v_tk_2521_);
v_a_2659_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2650_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2650_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
v___jp_2667_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_inc_ref_n(v___y_2681_, 2);
v___x_2689_ = l_Array_append___redArg(v___y_2681_, v___y_2688_);
lean_dec_ref(v___y_2688_);
lean_inc_n(v___y_2669_, 3);
lean_inc_n(v___y_2677_, 5);
v___x_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___y_2677_);
lean_ctor_set(v___x_2690_, 1, v___y_2669_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2677_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2694_ = l_Lean_Syntax_SepArray_ofElems(v___x_2693_, v___y_2671_);
lean_dec_ref(v___y_2671_);
v___x_2695_ = l_Array_append___redArg(v___y_2681_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___y_2677_);
lean_ctor_set(v___x_2696_, 1, v___y_2669_);
lean_ctor_set(v___x_2696_, 2, v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___y_2677_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_Syntax_node3(v___y_2677_, v___y_2669_, v___x_2692_, v___x_2696_, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node5(v___y_2677_, v___y_2678_, v___y_2670_, v___y_2675_, v___y_2685_, v___x_2690_, v___x_2699_);
v___y_2636_ = v___y_2680_;
v___y_2637_ = v___y_2673_;
v___y_2638_ = v___y_2683_;
v___y_2639_ = v___y_2676_;
v_stxForSuggestion_2640_ = v___x_2700_;
v___y_2641_ = v___y_2679_;
v___y_2642_ = v___y_2682_;
v___y_2643_ = v___y_2686_;
v___y_2644_ = v___y_2668_;
v___y_2645_ = v___y_2687_;
v___y_2646_ = v___y_2672_;
v___y_2647_ = v___y_2674_;
v___y_2648_ = v___y_2684_;
goto v___jp_2635_;
}
v___jp_2701_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_inc_ref(v___y_2717_);
v___x_2723_ = l_Array_append___redArg(v___y_2717_, v___y_2722_);
lean_dec_ref(v___y_2722_);
lean_inc(v___y_2703_);
lean_inc(v___y_2711_);
v___x_2724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2724_, 0, v___y_2711_);
lean_ctor_set(v___x_2724_, 1, v___y_2703_);
lean_ctor_set(v___x_2724_, 2, v___x_2723_);
if (lean_obj_tag(v___y_2707_) == 1)
{
lean_object* v_val_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_val_2725_ = lean_ctor_get(v___y_2707_, 0);
lean_inc(v_val_2725_);
lean_dec_ref_known(v___y_2707_, 1);
v___x_2726_ = l_Lean_SourceInfo_fromRef(v_val_2725_, v___x_2505_);
lean_dec(v_val_2725_);
v___x_2727_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Array_mkArray1___redArg(v___x_2728_);
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2712_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2714_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2719_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___x_2724_;
v___y_2686_ = v___y_2720_;
v___y_2687_ = v___y_2721_;
v___y_2688_ = v___x_2729_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v___y_2707_);
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2712_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2714_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2719_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___x_2724_;
v___y_2686_ = v___y_2720_;
v___y_2687_ = v___y_2721_;
v___y_2688_ = v___x_2730_;
goto v___jp_2667_;
}
}
v___jp_2731_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_inc_ref_n(v___y_2734_, 2);
v___x_2753_ = l_Array_append___redArg(v___y_2734_, v___y_2752_);
lean_dec_ref(v___y_2752_);
lean_inc_n(v___y_2750_, 3);
lean_inc_n(v___y_2737_, 5);
v___x_2754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2754_, 0, v___y_2737_);
lean_ctor_set(v___x_2754_, 1, v___y_2750_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2737_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2758_ = l_Lean_Syntax_SepArray_ofElems(v___x_2757_, v___y_2735_);
lean_dec_ref(v___y_2735_);
v___x_2759_ = l_Array_append___redArg(v___y_2734_, v___x_2758_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2737_);
lean_ctor_set(v___x_2760_, 1, v___y_2750_);
lean_ctor_set(v___x_2760_, 2, v___x_2759_);
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2737_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_Syntax_node3(v___y_2737_, v___y_2750_, v___x_2756_, v___x_2760_, v___x_2762_);
v___x_2764_ = l_Lean_Syntax_node5(v___y_2737_, v___y_2732_, v___y_2748_, v___y_2740_, v___y_2745_, v___x_2754_, v___x_2763_);
v___y_2636_ = v___y_2743_;
v___y_2637_ = v___y_2738_;
v___y_2638_ = v___y_2746_;
v___y_2639_ = v___y_2741_;
v_stxForSuggestion_2640_ = v___x_2764_;
v___y_2641_ = v___y_2742_;
v___y_2642_ = v___y_2744_;
v___y_2643_ = v___y_2749_;
v___y_2644_ = v___y_2733_;
v___y_2645_ = v___y_2751_;
v___y_2646_ = v___y_2736_;
v___y_2647_ = v___y_2739_;
v___y_2648_ = v___y_2747_;
goto v___jp_2635_;
}
v___jp_2765_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_inc_ref(v___y_2768_);
v___x_2787_ = l_Array_append___redArg(v___y_2768_, v___y_2786_);
lean_dec_ref(v___y_2786_);
lean_inc(v___y_2784_);
lean_inc(v___y_2772_);
v___x_2788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2788_, 0, v___y_2772_);
lean_ctor_set(v___x_2788_, 1, v___y_2784_);
lean_ctor_set(v___x_2788_, 2, v___x_2787_);
if (lean_obj_tag(v___y_2771_) == 1)
{
lean_object* v_val_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_val_2789_ = lean_ctor_get(v___y_2771_, 0);
lean_inc(v_val_2789_);
lean_dec_ref_known(v___y_2771_, 1);
v___x_2790_ = l_Lean_SourceInfo_fromRef(v_val_2789_, v___x_2505_);
lean_dec(v_val_2789_);
v___x_2791_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = l_Array_mkArray1___redArg(v___x_2792_);
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2772_;
v___y_2738_ = v___y_2773_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___x_2788_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2783_;
v___y_2749_ = v___y_2782_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___x_2793_;
goto v___jp_2731_;
}
else
{
lean_object* v___x_2794_; 
lean_dec(v___y_2771_);
v___x_2794_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2772_;
v___y_2738_ = v___y_2773_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___x_2788_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2783_;
v___y_2749_ = v___y_2782_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___x_2794_;
goto v___jp_2731_;
}
}
v___jp_2795_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_inc_ref_n(v___y_2796_, 2);
v___x_2816_ = l_Array_append___redArg(v___y_2796_, v___y_2815_);
lean_dec_ref(v___y_2815_);
lean_inc_n(v___y_2808_, 2);
lean_inc_n(v___y_2798_, 2);
v___x_2817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2817_, 0, v___y_2798_);
lean_ctor_set(v___x_2817_, 1, v___y_2808_);
lean_ctor_set(v___x_2817_, 2, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2818_, 0, v___y_2798_);
lean_ctor_set(v___x_2818_, 1, v___y_2808_);
lean_ctor_set(v___x_2818_, 2, v___y_2796_);
v___x_2819_ = l_Lean_Syntax_node5(v___y_2798_, v___y_2805_, v___y_2803_, v___y_2802_, v___y_2812_, v___x_2817_, v___x_2818_);
v___y_2636_ = v___y_2807_;
v___y_2637_ = v___y_2800_;
v___y_2638_ = v___y_2810_;
v___y_2639_ = v___y_2804_;
v_stxForSuggestion_2640_ = v___x_2819_;
v___y_2641_ = v___y_2806_;
v___y_2642_ = v___y_2809_;
v___y_2643_ = v___y_2813_;
v___y_2644_ = v___y_2797_;
v___y_2645_ = v___y_2814_;
v___y_2646_ = v___y_2799_;
v___y_2647_ = v___y_2801_;
v___y_2648_ = v___y_2811_;
goto v___jp_2635_;
}
v___jp_2820_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_inc_ref(v___y_2821_);
v___x_2841_ = l_Array_append___redArg(v___y_2821_, v___y_2840_);
lean_dec_ref(v___y_2840_);
lean_inc(v___y_2834_);
lean_inc(v___y_2823_);
v___x_2842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2842_, 0, v___y_2823_);
lean_ctor_set(v___x_2842_, 1, v___y_2834_);
lean_ctor_set(v___x_2842_, 2, v___x_2841_);
if (lean_obj_tag(v___y_2825_) == 1)
{
lean_object* v_val_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_val_2843_ = lean_ctor_get(v___y_2825_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v___y_2825_, 1);
v___x_2844_ = l_Lean_SourceInfo_fromRef(v_val_2843_, v___x_2505_);
lean_dec(v_val_2843_);
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Array_mkArray1___redArg(v___x_2846_);
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2826_;
v___y_2801_ = v___y_2827_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2829_;
v___y_2804_ = v___y_2830_;
v___y_2805_ = v___y_2831_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___y_2833_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2835_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___x_2842_;
v___y_2813_ = v___y_2838_;
v___y_2814_ = v___y_2839_;
v___y_2815_ = v___x_2847_;
goto v___jp_2795_;
}
else
{
lean_object* v___x_2848_; 
lean_dec(v___y_2825_);
v___x_2848_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2826_;
v___y_2801_ = v___y_2827_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2829_;
v___y_2804_ = v___y_2830_;
v___y_2805_ = v___y_2831_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___y_2833_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2835_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___x_2842_;
v___y_2813_ = v___y_2838_;
v___y_2814_ = v___y_2839_;
v___y_2815_ = v___x_2848_;
goto v___jp_2795_;
}
}
v___jp_2849_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_inc_ref_n(v___y_2850_, 2);
v___x_2870_ = l_Array_append___redArg(v___y_2850_, v___y_2869_);
lean_dec_ref(v___y_2869_);
lean_inc_n(v___y_2858_, 2);
lean_inc_n(v___y_2867_, 2);
v___x_2871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2871_, 0, v___y_2867_);
lean_ctor_set(v___x_2871_, 1, v___y_2858_);
lean_ctor_set(v___x_2871_, 2, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2867_);
lean_ctor_set(v___x_2872_, 1, v___y_2858_);
lean_ctor_set(v___x_2872_, 2, v___y_2850_);
v___x_2873_ = l_Lean_Syntax_node5(v___y_2867_, v___y_2852_, v___y_2853_, v___y_2857_, v___y_2865_, v___x_2871_, v___x_2872_);
v___y_2636_ = v___y_2861_;
v___y_2637_ = v___y_2855_;
v___y_2638_ = v___y_2863_;
v___y_2639_ = v___y_2859_;
v_stxForSuggestion_2640_ = v___x_2873_;
v___y_2641_ = v___y_2860_;
v___y_2642_ = v___y_2862_;
v___y_2643_ = v___y_2866_;
v___y_2644_ = v___y_2851_;
v___y_2645_ = v___y_2868_;
v___y_2646_ = v___y_2854_;
v___y_2647_ = v___y_2856_;
v___y_2648_ = v___y_2864_;
goto v___jp_2635_;
}
v___jp_2874_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_inc_ref(v___y_2875_);
v___x_2895_ = l_Array_append___redArg(v___y_2875_, v___y_2894_);
lean_dec_ref(v___y_2894_);
lean_inc(v___y_2884_);
lean_inc(v___y_2892_);
v___x_2896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2896_, 0, v___y_2892_);
lean_ctor_set(v___x_2896_, 1, v___y_2884_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
if (lean_obj_tag(v___y_2880_) == 1)
{
lean_object* v_val_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_val_2897_ = lean_ctor_get(v___y_2880_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v___y_2880_, 1);
v___x_2898_ = l_Lean_SourceInfo_fromRef(v_val_2897_, v___x_2505_);
lean_dec(v_val_2897_);
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Array_mkArray1___redArg(v___x_2900_);
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2882_;
v___y_2857_ = v___y_2883_;
v___y_2858_ = v___y_2884_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2886_;
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2890_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___x_2896_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___x_2901_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2902_; 
lean_dec(v___y_2880_);
v___x_2902_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2882_;
v___y_2857_ = v___y_2883_;
v___y_2858_ = v___y_2884_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2886_;
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2890_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___x_2896_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___x_2902_;
goto v___jp_2849_;
}
}
v___jp_2903_:
{
lean_object* v_ref_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_ref_2921_ = lean_ctor_get(v___y_2908_, 4);
v___x_2922_ = l_Lean_SourceInfo_fromRef(v_ref_2921_, v___y_2920_);
v___x_2923_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2924_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2923_);
v___x_2925_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_2926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2929_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2913_) == 1)
{
lean_object* v_val_2930_; lean_object* v___x_2931_; 
v_val_2930_ = lean_ctor_get(v___y_2913_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v___y_2913_, 1);
v___x_2931_ = l_Array_mkArray1___redArg(v_val_2930_);
v___y_2702_ = v___y_2904_;
v___y_2703_ = v___x_2928_;
v___y_2704_ = v___x_2927_;
v___y_2705_ = v___y_2905_;
v___y_2706_ = v___y_2906_;
v___y_2707_ = v___y_2907_;
v___y_2708_ = v___y_2909_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___y_2910_;
v___y_2711_ = v___x_2922_;
v___y_2712_ = v___y_2911_;
v___y_2713_ = v___y_2912_;
v___y_2714_ = v___x_2924_;
v___y_2715_ = v___y_2914_;
v___y_2716_ = v___y_2915_;
v___y_2717_ = v___x_2929_;
v___y_2718_ = v___y_2917_;
v___y_2719_ = v___y_2916_;
v___y_2720_ = v___y_2918_;
v___y_2721_ = v___y_2919_;
v___y_2722_ = v___x_2931_;
goto v___jp_2701_;
}
else
{
lean_object* v___x_2932_; 
lean_dec(v___y_2913_);
v___x_2932_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2702_ = v___y_2904_;
v___y_2703_ = v___x_2928_;
v___y_2704_ = v___x_2927_;
v___y_2705_ = v___y_2905_;
v___y_2706_ = v___y_2906_;
v___y_2707_ = v___y_2907_;
v___y_2708_ = v___y_2909_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___y_2910_;
v___y_2711_ = v___x_2922_;
v___y_2712_ = v___y_2911_;
v___y_2713_ = v___y_2912_;
v___y_2714_ = v___x_2924_;
v___y_2715_ = v___y_2914_;
v___y_2716_ = v___y_2915_;
v___y_2717_ = v___x_2929_;
v___y_2718_ = v___y_2917_;
v___y_2719_ = v___y_2916_;
v___y_2720_ = v___y_2918_;
v___y_2721_ = v___y_2919_;
v___y_2722_ = v___x_2932_;
goto v___jp_2701_;
}
}
v___jp_2933_:
{
lean_object* v___x_2950_; lean_object* v_a_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2950_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2936_);
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2950_);
v___x_2952_ = lean_array_get_size(v___y_2935_);
v___x_2953_ = lean_nat_dec_eq(v___x_2952_, v___x_2520_);
if (v___x_2953_ == 0)
{
if (lean_obj_tag(v___y_2937_) == 0)
{
v___y_2904_ = v___y_2945_;
v___y_2905_ = v___y_2935_;
v___y_2906_ = v___y_2947_;
v___y_2907_ = v___y_2938_;
v___y_2908_ = v___y_2948_;
v___y_2909_ = v___y_2940_;
v___y_2910_ = v_a_2951_;
v___y_2911_ = v_stxForExecution_2941_;
v___y_2912_ = v___y_2942_;
v___y_2913_ = v___y_2934_;
v___y_2914_ = v___y_2937_;
v___y_2915_ = v___y_2943_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2949_;
v___y_2918_ = v___y_2944_;
v___y_2919_ = v___y_2946_;
v___y_2920_ = v___x_2953_;
goto v___jp_2903_;
}
else
{
if (v___y_2940_ == 0)
{
v___y_2904_ = v___y_2945_;
v___y_2905_ = v___y_2935_;
v___y_2906_ = v___y_2947_;
v___y_2907_ = v___y_2938_;
v___y_2908_ = v___y_2948_;
v___y_2909_ = v___y_2940_;
v___y_2910_ = v_a_2951_;
v___y_2911_ = v_stxForExecution_2941_;
v___y_2912_ = v___y_2942_;
v___y_2913_ = v___y_2934_;
v___y_2914_ = v___y_2937_;
v___y_2915_ = v___y_2943_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2949_;
v___y_2918_ = v___y_2944_;
v___y_2919_ = v___y_2946_;
v___y_2920_ = v___y_2940_;
goto v___jp_2903_;
}
else
{
lean_object* v_ref_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_ref_2954_ = lean_ctor_get(v___y_2948_, 4);
v___x_2955_ = l_Lean_SourceInfo_fromRef(v_ref_2954_, v___x_2953_);
v___x_2956_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2957_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2956_);
v___x_2958_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2962_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2934_) == 1)
{
lean_object* v_val_2963_; lean_object* v___x_2964_; 
v_val_2963_ = lean_ctor_get(v___y_2934_, 0);
lean_inc(v_val_2963_);
lean_dec_ref_known(v___y_2934_, 1);
v___x_2964_ = l_Array_mkArray1___redArg(v_val_2963_);
v___y_2766_ = v___x_2957_;
v___y_2767_ = v___y_2945_;
v___y_2768_ = v___x_2962_;
v___y_2769_ = v___y_2935_;
v___y_2770_ = v___y_2947_;
v___y_2771_ = v___y_2938_;
v___y_2772_ = v___x_2955_;
v___y_2773_ = v___y_2940_;
v___y_2774_ = v___y_2948_;
v___y_2775_ = v_a_2951_;
v___y_2776_ = v_stxForExecution_2941_;
v___y_2777_ = v___y_2942_;
v___y_2778_ = v___y_2937_;
v___y_2779_ = v___y_2943_;
v___y_2780_ = v___y_2949_;
v___y_2781_ = v___y_2939_;
v___y_2782_ = v___y_2944_;
v___y_2783_ = v___x_2960_;
v___y_2784_ = v___x_2961_;
v___y_2785_ = v___y_2946_;
v___y_2786_ = v___x_2964_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2965_; 
lean_dec(v___y_2934_);
v___x_2965_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2766_ = v___x_2957_;
v___y_2767_ = v___y_2945_;
v___y_2768_ = v___x_2962_;
v___y_2769_ = v___y_2935_;
v___y_2770_ = v___y_2947_;
v___y_2771_ = v___y_2938_;
v___y_2772_ = v___x_2955_;
v___y_2773_ = v___y_2940_;
v___y_2774_ = v___y_2948_;
v___y_2775_ = v_a_2951_;
v___y_2776_ = v_stxForExecution_2941_;
v___y_2777_ = v___y_2942_;
v___y_2778_ = v___y_2937_;
v___y_2779_ = v___y_2943_;
v___y_2780_ = v___y_2949_;
v___y_2781_ = v___y_2939_;
v___y_2782_ = v___y_2944_;
v___y_2783_ = v___x_2960_;
v___y_2784_ = v___x_2961_;
v___y_2785_ = v___y_2946_;
v___y_2786_ = v___x_2965_;
goto v___jp_2765_;
}
}
}
}
else
{
lean_dec_ref(v___y_2935_);
if (lean_obj_tag(v___y_2937_) == 0)
{
lean_object* v_ref_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_ref_2966_ = lean_ctor_get(v___y_2948_, 4);
v___x_2967_ = 0;
v___x_2968_ = l_Lean_SourceInfo_fromRef(v_ref_2966_, v___x_2967_);
v___x_2969_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2970_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2969_);
v___x_2971_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2975_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2934_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2977_; 
v_val_2976_ = lean_ctor_get(v___y_2934_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___y_2934_, 1);
v___x_2977_ = l_Array_mkArray1___redArg(v_val_2976_);
v___y_2821_ = v___x_2975_;
v___y_2822_ = v___y_2945_;
v___y_2823_ = v___x_2968_;
v___y_2824_ = v___y_2947_;
v___y_2825_ = v___y_2938_;
v___y_2826_ = v___y_2940_;
v___y_2827_ = v___y_2948_;
v___y_2828_ = v_a_2951_;
v___y_2829_ = v___x_2973_;
v___y_2830_ = v_stxForExecution_2941_;
v___y_2831_ = v___x_2970_;
v___y_2832_ = v___y_2942_;
v___y_2833_ = v___y_2937_;
v___y_2834_ = v___x_2974_;
v___y_2835_ = v___y_2943_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___y_2939_;
v___y_2838_ = v___y_2944_;
v___y_2839_ = v___y_2946_;
v___y_2840_ = v___x_2977_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2978_; 
lean_dec(v___y_2934_);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2821_ = v___x_2975_;
v___y_2822_ = v___y_2945_;
v___y_2823_ = v___x_2968_;
v___y_2824_ = v___y_2947_;
v___y_2825_ = v___y_2938_;
v___y_2826_ = v___y_2940_;
v___y_2827_ = v___y_2948_;
v___y_2828_ = v_a_2951_;
v___y_2829_ = v___x_2973_;
v___y_2830_ = v_stxForExecution_2941_;
v___y_2831_ = v___x_2970_;
v___y_2832_ = v___y_2942_;
v___y_2833_ = v___y_2937_;
v___y_2834_ = v___x_2974_;
v___y_2835_ = v___y_2943_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___y_2939_;
v___y_2838_ = v___y_2944_;
v___y_2839_ = v___y_2946_;
v___y_2840_ = v___x_2978_;
goto v___jp_2820_;
}
}
else
{
lean_object* v_ref_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_ref_2979_ = lean_ctor_get(v___y_2948_, 4);
v___x_2980_ = 0;
v___x_2981_ = l_Lean_SourceInfo_fromRef(v_ref_2979_, v___x_2980_);
v___x_2982_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2983_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2982_);
v___x_2984_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2988_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2934_) == 1)
{
lean_object* v_val_2989_; lean_object* v___x_2990_; 
v_val_2989_ = lean_ctor_get(v___y_2934_, 0);
lean_inc(v_val_2989_);
lean_dec_ref_known(v___y_2934_, 1);
v___x_2990_ = l_Array_mkArray1___redArg(v_val_2989_);
v___y_2875_ = v___x_2988_;
v___y_2876_ = v___y_2945_;
v___y_2877_ = v___x_2983_;
v___y_2878_ = v___x_2986_;
v___y_2879_ = v___y_2947_;
v___y_2880_ = v___y_2938_;
v___y_2881_ = v___y_2940_;
v___y_2882_ = v___y_2948_;
v___y_2883_ = v_a_2951_;
v___y_2884_ = v___x_2987_;
v___y_2885_ = v_stxForExecution_2941_;
v___y_2886_ = v___y_2942_;
v___y_2887_ = v___y_2937_;
v___y_2888_ = v___y_2943_;
v___y_2889_ = v___y_2949_;
v___y_2890_ = v___y_2939_;
v___y_2891_ = v___y_2944_;
v___y_2892_ = v___x_2981_;
v___y_2893_ = v___y_2946_;
v___y_2894_ = v___x_2990_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2991_; 
lean_dec(v___y_2934_);
v___x_2991_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2875_ = v___x_2988_;
v___y_2876_ = v___y_2945_;
v___y_2877_ = v___x_2983_;
v___y_2878_ = v___x_2986_;
v___y_2879_ = v___y_2947_;
v___y_2880_ = v___y_2938_;
v___y_2881_ = v___y_2940_;
v___y_2882_ = v___y_2948_;
v___y_2883_ = v_a_2951_;
v___y_2884_ = v___x_2987_;
v___y_2885_ = v_stxForExecution_2941_;
v___y_2886_ = v___y_2942_;
v___y_2887_ = v___y_2937_;
v___y_2888_ = v___y_2943_;
v___y_2889_ = v___y_2949_;
v___y_2890_ = v___y_2939_;
v___y_2891_ = v___y_2944_;
v___y_2892_ = v___x_2981_;
v___y_2893_ = v___y_2946_;
v___y_2894_ = v___x_2991_;
goto v___jp_2874_;
}
}
}
}
v___jp_2992_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_inc_ref_n(v___y_3003_, 2);
v___x_3015_ = l_Array_append___redArg(v___y_3003_, v___y_3014_);
lean_dec_ref(v___y_3014_);
lean_inc_n(v___y_2997_, 3);
lean_inc_n(v___y_3004_, 5);
v___x_3016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3016_, 0, v___y_3004_);
lean_ctor_set(v___x_3016_, 1, v___y_2997_);
lean_ctor_set(v___x_3016_, 2, v___x_3015_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___y_3004_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3020_ = l_Lean_Syntax_SepArray_ofElems(v___x_3019_, v___y_2993_);
v___x_3021_ = l_Array_append___redArg(v___y_3003_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3022_, 0, v___y_3004_);
lean_ctor_set(v___x_3022_, 1, v___y_2997_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
v___x_3023_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___y_3004_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_Syntax_node3(v___y_3004_, v___y_2997_, v___x_3018_, v___x_3022_, v___x_3024_);
lean_inc(v___y_2995_);
v___x_3026_ = l_Lean_Syntax_node5(v___y_3004_, v___y_3008_, v___y_3006_, v___y_2995_, v___y_3009_, v___x_3016_, v___x_3025_);
v___y_2934_ = v___y_3005_;
v___y_2935_ = v___y_2993_;
v___y_2936_ = v___y_2995_;
v___y_2937_ = v___y_3007_;
v___y_2938_ = v___y_2996_;
v___y_2939_ = v___y_3010_;
v___y_2940_ = v___y_2998_;
v_stxForExecution_2941_ = v___x_3026_;
v___y_2942_ = v___y_3000_;
v___y_2943_ = v___y_2994_;
v___y_2944_ = v___y_2999_;
v___y_2945_ = v___y_3001_;
v___y_2946_ = v___y_3002_;
v___y_2947_ = v___y_3012_;
v___y_2948_ = v___y_3013_;
v___y_2949_ = v___y_3011_;
goto v___jp_2933_;
}
v___jp_3027_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_inc_ref(v___y_3038_);
v___x_3049_ = l_Array_append___redArg(v___y_3038_, v___y_3048_);
lean_dec_ref(v___y_3048_);
lean_inc(v___y_3032_);
lean_inc(v___y_3039_);
v___x_3050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3050_, 0, v___y_3039_);
lean_ctor_set(v___x_3050_, 1, v___y_3032_);
lean_ctor_set(v___x_3050_, 2, v___x_3049_);
if (lean_obj_tag(v___y_3031_) == 1)
{
lean_object* v_val_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_val_3051_ = lean_ctor_get(v___y_3031_, 0);
v___x_3052_ = l_Lean_SourceInfo_fromRef(v_val_3051_, v___x_2505_);
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Array_mkArray1___redArg(v___x_3054_);
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3039_;
v___y_3005_ = v___y_3041_;
v___y_3006_ = v___y_3040_;
v___y_3007_ = v___y_3042_;
v___y_3008_ = v___y_3043_;
v___y_3009_ = v___x_3050_;
v___y_3010_ = v___y_3044_;
v___y_3011_ = v___y_3045_;
v___y_3012_ = v___y_3046_;
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___x_3055_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_3056_; 
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3039_;
v___y_3005_ = v___y_3041_;
v___y_3006_ = v___y_3040_;
v___y_3007_ = v___y_3042_;
v___y_3008_ = v___y_3043_;
v___y_3009_ = v___x_3050_;
v___y_3010_ = v___y_3044_;
v___y_3011_ = v___y_3045_;
v___y_3012_ = v___y_3046_;
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___x_3056_;
goto v___jp_2992_;
}
}
v___jp_3057_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_inc_ref_n(v___y_3064_, 2);
v___x_3080_ = l_Array_append___redArg(v___y_3064_, v___y_3079_);
lean_dec_ref(v___y_3079_);
lean_inc_n(v___y_3076_, 3);
lean_inc_n(v___y_3068_, 5);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3068_);
lean_ctor_set(v___x_3081_, 1, v___y_3076_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3068_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3085_ = l_Lean_Syntax_SepArray_ofElems(v___x_3084_, v___y_3059_);
v___x_3086_ = l_Array_append___redArg(v___y_3064_, v___x_3085_);
lean_dec_ref(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3087_, 0, v___y_3068_);
lean_ctor_set(v___x_3087_, 1, v___y_3076_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
v___x_3088_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___y_3068_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_Syntax_node3(v___y_3068_, v___y_3076_, v___x_3083_, v___x_3087_, v___x_3089_);
lean_inc(v___y_3062_);
v___x_3091_ = l_Lean_Syntax_node5(v___y_3068_, v___y_3071_, v___y_3061_, v___y_3062_, v___y_3058_, v___x_3081_, v___x_3090_);
v___y_2934_ = v___y_3072_;
v___y_2935_ = v___y_3059_;
v___y_2936_ = v___y_3062_;
v___y_2937_ = v___y_3073_;
v___y_2938_ = v___y_3063_;
v___y_2939_ = v___y_3074_;
v___y_2940_ = v___y_3065_;
v_stxForExecution_2941_ = v___x_3091_;
v___y_2942_ = v___y_3067_;
v___y_2943_ = v___y_3060_;
v___y_2944_ = v___y_3066_;
v___y_2945_ = v___y_3069_;
v___y_2946_ = v___y_3070_;
v___y_2947_ = v___y_3077_;
v___y_2948_ = v___y_3078_;
v___y_2949_ = v___y_3075_;
goto v___jp_2933_;
}
v___jp_3092_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_inc_ref(v___y_3097_);
v___x_3114_ = l_Array_append___redArg(v___y_3097_, v___y_3113_);
lean_dec_ref(v___y_3113_);
lean_inc(v___y_3110_);
lean_inc(v___y_3102_);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___y_3102_);
lean_ctor_set(v___x_3115_, 1, v___y_3110_);
lean_ctor_set(v___x_3115_, 2, v___x_3114_);
if (lean_obj_tag(v___y_3098_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_val_3116_ = lean_ctor_get(v___y_3098_, 0);
v___x_3117_ = l_Lean_SourceInfo_fromRef(v_val_3116_, v___x_2505_);
v___x_3118_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Array_mkArray1___redArg(v___x_3119_);
v___y_3058_ = v___x_3115_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3103_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___x_3120_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3058_ = v___x_3115_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3103_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___x_3121_;
goto v___jp_3057_;
}
}
v___jp_3122_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_inc_ref_n(v___y_3127_, 2);
v___x_3145_ = l_Array_append___redArg(v___y_3127_, v___y_3144_);
lean_dec_ref(v___y_3144_);
lean_inc_n(v___y_3129_, 2);
lean_inc_n(v___y_3137_, 2);
v___x_3146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3146_, 0, v___y_3137_);
lean_ctor_set(v___x_3146_, 1, v___y_3129_);
lean_ctor_set(v___x_3146_, 2, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___y_3137_);
lean_ctor_set(v___x_3147_, 1, v___y_3129_);
lean_ctor_set(v___x_3147_, 2, v___y_3127_);
lean_inc(v___y_3125_);
v___x_3148_ = l_Lean_Syntax_node5(v___y_3137_, v___y_3134_, v___y_3132_, v___y_3125_, v___y_3135_, v___x_3146_, v___x_3147_);
v___y_2934_ = v___y_3138_;
v___y_2935_ = v___y_3123_;
v___y_2936_ = v___y_3125_;
v___y_2937_ = v___y_3139_;
v___y_2938_ = v___y_3126_;
v___y_2939_ = v___y_3140_;
v___y_2940_ = v___y_3128_;
v_stxForExecution_2941_ = v___x_3148_;
v___y_2942_ = v___y_3131_;
v___y_2943_ = v___y_3124_;
v___y_2944_ = v___y_3130_;
v___y_2945_ = v___y_3133_;
v___y_2946_ = v___y_3136_;
v___y_2947_ = v___y_3142_;
v___y_2948_ = v___y_3143_;
v___y_2949_ = v___y_3141_;
goto v___jp_2933_;
}
v___jp_3149_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_inc_ref(v___y_3154_);
v___x_3171_ = l_Array_append___redArg(v___y_3154_, v___y_3170_);
lean_dec_ref(v___y_3170_);
lean_inc(v___y_3156_);
lean_inc(v___y_3163_);
v___x_3172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3172_, 0, v___y_3163_);
lean_ctor_set(v___x_3172_, 1, v___y_3156_);
lean_ctor_set(v___x_3172_, 2, v___x_3171_);
if (lean_obj_tag(v___y_3153_) == 1)
{
lean_object* v_val_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_val_3173_ = lean_ctor_get(v___y_3153_, 0);
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_val_3173_, v___x_2505_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Array_mkArray1___redArg(v___x_3176_);
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v___x_3172_;
v___y_3136_ = v___y_3161_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3165_;
v___y_3140_ = v___y_3166_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___x_3177_;
goto v___jp_3122_;
}
else
{
lean_object* v___x_3178_; 
v___x_3178_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v___x_3172_;
v___y_3136_ = v___y_3161_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3165_;
v___y_3140_ = v___y_3166_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___x_3178_;
goto v___jp_3122_;
}
}
v___jp_3179_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_inc_ref_n(v___y_3191_, 2);
v___x_3202_ = l_Array_append___redArg(v___y_3191_, v___y_3201_);
lean_dec_ref(v___y_3201_);
lean_inc_n(v___y_3193_, 2);
lean_inc_n(v___y_3194_, 2);
v___x_3203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3203_, 0, v___y_3194_);
lean_ctor_set(v___x_3203_, 1, v___y_3193_);
lean_ctor_set(v___x_3203_, 2, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3194_);
lean_ctor_set(v___x_3204_, 1, v___y_3193_);
lean_ctor_set(v___x_3204_, 2, v___y_3191_);
lean_inc(v___y_3183_);
v___x_3205_ = l_Lean_Syntax_node5(v___y_3194_, v___y_3180_, v___y_3198_, v___y_3183_, v___y_3188_, v___x_3203_, v___x_3204_);
v___y_2934_ = v___y_3192_;
v___y_2935_ = v___y_3181_;
v___y_2936_ = v___y_3183_;
v___y_2937_ = v___y_3195_;
v___y_2938_ = v___y_3184_;
v___y_2939_ = v___y_3196_;
v___y_2940_ = v___y_3185_;
v_stxForExecution_2941_ = v___x_3205_;
v___y_2942_ = v___y_3187_;
v___y_2943_ = v___y_3182_;
v___y_2944_ = v___y_3186_;
v___y_2945_ = v___y_3189_;
v___y_2946_ = v___y_3190_;
v___y_2947_ = v___y_3199_;
v___y_2948_ = v___y_3200_;
v___y_2949_ = v___y_3197_;
goto v___jp_2933_;
}
v___jp_3206_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_inc_ref(v___y_3217_);
v___x_3228_ = l_Array_append___redArg(v___y_3217_, v___y_3227_);
lean_dec_ref(v___y_3227_);
lean_inc(v___y_3219_);
lean_inc(v___y_3220_);
v___x_3229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___y_3220_);
lean_ctor_set(v___x_3229_, 1, v___y_3219_);
lean_ctor_set(v___x_3229_, 2, v___x_3228_);
if (lean_obj_tag(v___y_3211_) == 1)
{
lean_object* v_val_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_val_3230_ = lean_ctor_get(v___y_3211_, 0);
v___x_3231_ = l_Lean_SourceInfo_fromRef(v_val_3230_, v___x_2505_);
v___x_3232_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Array_mkArray1___redArg(v___x_3233_);
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___x_3229_;
v___y_3189_ = v___y_3215_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3220_;
v___y_3195_ = v___y_3221_;
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3224_;
v___y_3198_ = v___y_3223_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___x_3234_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___x_3229_;
v___y_3189_ = v___y_3215_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3220_;
v___y_3195_ = v___y_3221_;
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3224_;
v___y_3198_ = v___y_3223_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___x_3235_;
goto v___jp_3179_;
}
}
v___jp_3236_:
{
lean_object* v_ref_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_ref_3253_ = lean_ctor_get(v___y_3251_, 4);
v___x_3254_ = l_Lean_SourceInfo_fromRef(v_ref_3253_, v___y_3252_);
v___x_3255_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3256_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3255_);
v___x_3257_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_3258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3261_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3246_) == 1)
{
lean_object* v_val_3262_; lean_object* v___x_3263_; 
v_val_3262_ = lean_ctor_get(v___y_3246_, 0);
lean_inc(v_val_3262_);
v___x_3263_ = l_Array_mkArray1___redArg(v_val_3262_);
v___y_3028_ = v___y_3237_;
v___y_3029_ = v___y_3238_;
v___y_3030_ = v___y_3239_;
v___y_3031_ = v___y_3240_;
v___y_3032_ = v___x_3260_;
v___y_3033_ = v___y_3241_;
v___y_3034_ = v___y_3242_;
v___y_3035_ = v___y_3243_;
v___y_3036_ = v___y_3244_;
v___y_3037_ = v___y_3245_;
v___y_3038_ = v___x_3261_;
v___y_3039_ = v___x_3254_;
v___y_3040_ = v___x_3259_;
v___y_3041_ = v___y_3246_;
v___y_3042_ = v___y_3247_;
v___y_3043_ = v___x_3256_;
v___y_3044_ = v___y_3248_;
v___y_3045_ = v___y_3249_;
v___y_3046_ = v___y_3250_;
v___y_3047_ = v___y_3251_;
v___y_3048_ = v___x_3263_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3264_; 
v___x_3264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3028_ = v___y_3237_;
v___y_3029_ = v___y_3238_;
v___y_3030_ = v___y_3239_;
v___y_3031_ = v___y_3240_;
v___y_3032_ = v___x_3260_;
v___y_3033_ = v___y_3241_;
v___y_3034_ = v___y_3242_;
v___y_3035_ = v___y_3243_;
v___y_3036_ = v___y_3244_;
v___y_3037_ = v___y_3245_;
v___y_3038_ = v___x_3261_;
v___y_3039_ = v___x_3254_;
v___y_3040_ = v___x_3259_;
v___y_3041_ = v___y_3246_;
v___y_3042_ = v___y_3247_;
v___y_3043_ = v___x_3256_;
v___y_3044_ = v___y_3248_;
v___y_3045_ = v___y_3249_;
v___y_3046_ = v___y_3250_;
v___y_3047_ = v___y_3251_;
v___y_3048_ = v___x_3264_;
goto v___jp_3027_;
}
}
v___jp_3265_:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = lean_array_get_size(v_argsArray_3272_);
v___x_3282_ = lean_nat_dec_eq(v___x_3281_, v___x_2520_);
if (v___x_3282_ == 0)
{
if (lean_obj_tag(v___y_3267_) == 0)
{
v___y_3237_ = v_argsArray_3272_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3268_;
v___y_3240_ = v___y_3269_;
v___y_3241_ = v___y_3270_;
v___y_3242_ = v___y_3275_;
v___y_3243_ = v___y_3273_;
v___y_3244_ = v___y_3276_;
v___y_3245_ = v___y_3277_;
v___y_3246_ = v___y_3266_;
v___y_3247_ = v___y_3267_;
v___y_3248_ = v___y_3271_;
v___y_3249_ = v___y_3280_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___x_3282_;
goto v___jp_3236_;
}
else
{
if (v___y_3270_ == 0)
{
v___y_3237_ = v_argsArray_3272_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3268_;
v___y_3240_ = v___y_3269_;
v___y_3241_ = v___y_3270_;
v___y_3242_ = v___y_3275_;
v___y_3243_ = v___y_3273_;
v___y_3244_ = v___y_3276_;
v___y_3245_ = v___y_3277_;
v___y_3246_ = v___y_3266_;
v___y_3247_ = v___y_3267_;
v___y_3248_ = v___y_3271_;
v___y_3249_ = v___y_3280_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3270_;
goto v___jp_3236_;
}
else
{
lean_object* v_ref_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_ref_3283_ = lean_ctor_get(v___y_3279_, 4);
v___x_3284_ = l_Lean_SourceInfo_fromRef(v_ref_3283_, v___x_3282_);
v___x_3285_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3286_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3285_);
v___x_3287_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3291_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3266_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3293_; 
v_val_3292_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3292_);
v___x_3293_ = l_Array_mkArray1___redArg(v_val_3292_);
v___y_3093_ = v_argsArray_3272_;
v___y_3094_ = v___y_3274_;
v___y_3095_ = v___x_3289_;
v___y_3096_ = v___y_3268_;
v___y_3097_ = v___x_3291_;
v___y_3098_ = v___y_3269_;
v___y_3099_ = v___y_3270_;
v___y_3100_ = v___y_3275_;
v___y_3101_ = v___y_3273_;
v___y_3102_ = v___x_3284_;
v___y_3103_ = v___y_3276_;
v___y_3104_ = v___y_3277_;
v___y_3105_ = v___x_3286_;
v___y_3106_ = v___y_3266_;
v___y_3107_ = v___y_3267_;
v___y_3108_ = v___y_3271_;
v___y_3109_ = v___y_3280_;
v___y_3110_ = v___x_3290_;
v___y_3111_ = v___y_3278_;
v___y_3112_ = v___y_3279_;
v___y_3113_ = v___x_3293_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3294_; 
v___x_3294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3093_ = v_argsArray_3272_;
v___y_3094_ = v___y_3274_;
v___y_3095_ = v___x_3289_;
v___y_3096_ = v___y_3268_;
v___y_3097_ = v___x_3291_;
v___y_3098_ = v___y_3269_;
v___y_3099_ = v___y_3270_;
v___y_3100_ = v___y_3275_;
v___y_3101_ = v___y_3273_;
v___y_3102_ = v___x_3284_;
v___y_3103_ = v___y_3276_;
v___y_3104_ = v___y_3277_;
v___y_3105_ = v___x_3286_;
v___y_3106_ = v___y_3266_;
v___y_3107_ = v___y_3267_;
v___y_3108_ = v___y_3271_;
v___y_3109_ = v___y_3280_;
v___y_3110_ = v___x_3290_;
v___y_3111_ = v___y_3278_;
v___y_3112_ = v___y_3279_;
v___y_3113_ = v___x_3294_;
goto v___jp_3092_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3267_) == 0)
{
lean_object* v_ref_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_ref_3295_ = lean_ctor_get(v___y_3279_, 4);
v___x_3296_ = 0;
v___x_3297_ = l_Lean_SourceInfo_fromRef(v_ref_3295_, v___x_3296_);
v___x_3298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3299_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3298_);
v___x_3300_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3304_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3266_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3305_);
v___x_3306_ = l_Array_mkArray1___redArg(v_val_3305_);
v___y_3150_ = v_argsArray_3272_;
v___y_3151_ = v___y_3274_;
v___y_3152_ = v___y_3268_;
v___y_3153_ = v___y_3269_;
v___y_3154_ = v___x_3304_;
v___y_3155_ = v___y_3270_;
v___y_3156_ = v___x_3303_;
v___y_3157_ = v___y_3275_;
v___y_3158_ = v___y_3273_;
v___y_3159_ = v___x_3302_;
v___y_3160_ = v___y_3276_;
v___y_3161_ = v___y_3277_;
v___y_3162_ = v___x_3299_;
v___y_3163_ = v___x_3297_;
v___y_3164_ = v___y_3266_;
v___y_3165_ = v___y_3267_;
v___y_3166_ = v___y_3271_;
v___y_3167_ = v___y_3280_;
v___y_3168_ = v___y_3278_;
v___y_3169_ = v___y_3279_;
v___y_3170_ = v___x_3306_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3150_ = v_argsArray_3272_;
v___y_3151_ = v___y_3274_;
v___y_3152_ = v___y_3268_;
v___y_3153_ = v___y_3269_;
v___y_3154_ = v___x_3304_;
v___y_3155_ = v___y_3270_;
v___y_3156_ = v___x_3303_;
v___y_3157_ = v___y_3275_;
v___y_3158_ = v___y_3273_;
v___y_3159_ = v___x_3302_;
v___y_3160_ = v___y_3276_;
v___y_3161_ = v___y_3277_;
v___y_3162_ = v___x_3299_;
v___y_3163_ = v___x_3297_;
v___y_3164_ = v___y_3266_;
v___y_3165_ = v___y_3267_;
v___y_3166_ = v___y_3271_;
v___y_3167_ = v___y_3280_;
v___y_3168_ = v___y_3278_;
v___y_3169_ = v___y_3279_;
v___y_3170_ = v___x_3307_;
goto v___jp_3149_;
}
}
else
{
lean_object* v_ref_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_ref_3308_ = lean_ctor_get(v___y_3279_, 4);
v___x_3309_ = 0;
v___x_3310_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v___x_3309_);
v___x_3311_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3312_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3311_);
v___x_3313_ = l_Lean_SourceInfo_fromRef(v_tk_2521_, v___x_2505_);
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3317_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3266_) == 1)
{
lean_object* v_val_3318_; lean_object* v___x_3319_; 
v_val_3318_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3318_);
v___x_3319_ = l_Array_mkArray1___redArg(v_val_3318_);
v___y_3207_ = v___x_3312_;
v___y_3208_ = v_argsArray_3272_;
v___y_3209_ = v___y_3274_;
v___y_3210_ = v___y_3268_;
v___y_3211_ = v___y_3269_;
v___y_3212_ = v___y_3270_;
v___y_3213_ = v___y_3275_;
v___y_3214_ = v___y_3273_;
v___y_3215_ = v___y_3276_;
v___y_3216_ = v___y_3277_;
v___y_3217_ = v___x_3317_;
v___y_3218_ = v___y_3266_;
v___y_3219_ = v___x_3316_;
v___y_3220_ = v___x_3310_;
v___y_3221_ = v___y_3267_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___x_3315_;
v___y_3224_ = v___y_3280_;
v___y_3225_ = v___y_3278_;
v___y_3226_ = v___y_3279_;
v___y_3227_ = v___x_3319_;
goto v___jp_3206_;
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3207_ = v___x_3312_;
v___y_3208_ = v_argsArray_3272_;
v___y_3209_ = v___y_3274_;
v___y_3210_ = v___y_3268_;
v___y_3211_ = v___y_3269_;
v___y_3212_ = v___y_3270_;
v___y_3213_ = v___y_3275_;
v___y_3214_ = v___y_3273_;
v___y_3215_ = v___y_3276_;
v___y_3216_ = v___y_3277_;
v___y_3217_ = v___x_3317_;
v___y_3218_ = v___y_3266_;
v___y_3219_ = v___x_3316_;
v___y_3220_ = v___x_3310_;
v___y_3221_ = v___y_3267_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___x_3315_;
v___y_3224_ = v___y_3280_;
v___y_3225_ = v___y_3278_;
v___y_3226_ = v___y_3279_;
v___y_3227_ = v___x_3320_;
goto v___jp_3206_;
}
}
}
}
v___jp_3321_:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3326_, v___y_3336_, v___y_3322_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = l_Lean_LibrarySuggestions_select(v_a_3339_, v___y_3337_, v___y_3336_, v___y_3322_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; size_t v_sz_3342_; size_t v___x_3343_; lean_object* v___x_3344_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v_sz_3342_ = lean_array_size(v_a_3341_);
v___x_3343_ = ((size_t)0ULL);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3341_, v_sz_3342_, v___x_3343_, v___y_3328_, v___y_3329_, v___y_3326_, v___y_3333_, v___y_3323_, v___y_3336_, v___y_3322_, v___y_3330_, v___y_3331_);
lean_dec(v_a_3341_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___y_3266_ = v___y_3332_;
v___y_3267_ = v___y_3334_;
v___y_3268_ = v___y_3324_;
v___y_3269_ = v___y_3325_;
v___y_3270_ = v___y_3327_;
v___y_3271_ = v___y_3335_;
v_argsArray_3272_ = v_a_3345_;
v___y_3273_ = v___y_3329_;
v___y_3274_ = v___y_3326_;
v___y_3275_ = v___y_3333_;
v___y_3276_ = v___y_3323_;
v___y_3277_ = v___y_3336_;
v___y_3278_ = v___y_3322_;
v___y_3279_ = v___y_3330_;
v___y_3280_ = v___y_3331_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v___y_3334_);
lean_dec(v___y_3332_);
lean_dec(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v_a_3346_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3344_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3344_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v___y_3334_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v_a_3354_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3340_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3340_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3334_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v_a_3362_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3338_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3338_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
v___jp_3370_:
{
lean_object* v_config_3387_; uint8_t v_suggestions_3388_; 
v_config_3387_ = lean_ctor_get(v___y_3383_, 0);
lean_inc_ref(v_config_3387_);
lean_dec_ref(v___y_3383_);
v_suggestions_3388_ = lean_ctor_get_uint8(v_config_3387_, sizeof(void*)*3 + 26);
if (v_suggestions_3388_ == 0)
{
lean_dec_ref(v_config_3387_);
lean_dec_ref(v___f_2509_);
v___y_3266_ = v___y_3380_;
v___y_3267_ = v___y_3382_;
v___y_3268_ = v___y_3373_;
v___y_3269_ = v___y_3374_;
v___y_3270_ = v___y_3376_;
v___y_3271_ = v___y_3384_;
v_argsArray_3272_ = v___y_3386_;
v___y_3273_ = v___y_3377_;
v___y_3274_ = v___y_3375_;
v___y_3275_ = v___y_3381_;
v___y_3276_ = v___y_3372_;
v___y_3277_ = v___y_3385_;
v___y_3278_ = v___y_3371_;
v___y_3279_ = v___y_3378_;
v___y_3280_ = v___y_3379_;
goto v___jp_3265_;
}
else
{
lean_object* v_maxSuggestions_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_maxSuggestions_3389_ = lean_ctor_get(v_config_3387_, 2);
lean_inc(v_maxSuggestions_3389_);
lean_dec_ref(v_config_3387_);
v___x_3390_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3391_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3389_) == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_unsigned_to_nat(100u);
v___x_3393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3390_);
lean_ctor_set(v___x_3393_, 2, v___f_2509_);
lean_ctor_set(v___x_3393_, 3, v___x_3391_);
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___y_3374_;
v___y_3326_ = v___y_3375_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3386_;
v___y_3329_ = v___y_3377_;
v___y_3330_ = v___y_3378_;
v___y_3331_ = v___y_3379_;
v___y_3332_ = v___y_3380_;
v___y_3333_ = v___y_3381_;
v___y_3334_ = v___y_3382_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
v___y_3337_ = v___x_3393_;
goto v___jp_3321_;
}
else
{
lean_object* v_val_3394_; lean_object* v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_maxSuggestions_3389_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v_maxSuggestions_3389_, 1);
v___x_3395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3395_, 0, v_val_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3390_);
lean_ctor_set(v___x_3395_, 2, v___f_2509_);
lean_ctor_set(v___x_3395_, 3, v___x_3391_);
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___y_3374_;
v___y_3326_ = v___y_3375_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3386_;
v___y_3329_ = v___y_3377_;
v___y_3330_ = v___y_3378_;
v___y_3331_ = v___y_3379_;
v___y_3332_ = v___y_3380_;
v___y_3333_ = v___y_3381_;
v___y_3334_ = v___y_3382_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
v___y_3337_ = v___x_3395_;
goto v___jp_3321_;
}
}
}
v___jp_3396_:
{
uint8_t v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = 1;
lean_inc(v___y_3397_);
v___x_3412_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3397_, v___x_3411_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3412_) == 0)
{
if (lean_obj_tag(v___y_3403_) == 1)
{
lean_object* v_a_3413_; lean_object* v_val_3414_; lean_object* v___x_3415_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v_val_3414_ = lean_ctor_get(v___y_3403_, 0);
lean_inc(v_val_3414_);
lean_dec_ref_known(v___y_3403_, 1);
v___x_3415_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3414_);
lean_dec(v_val_3414_);
v___y_3371_ = v___y_3398_;
v___y_3372_ = v___y_3399_;
v___y_3373_ = v___y_3397_;
v___y_3374_ = v___y_3400_;
v___y_3375_ = v___y_3401_;
v___y_3376_ = v___y_3402_;
v___y_3377_ = v___y_3404_;
v___y_3378_ = v___y_3405_;
v___y_3379_ = v___y_3406_;
v___y_3380_ = v___y_3410_;
v___y_3381_ = v___y_3407_;
v___y_3382_ = v___y_3408_;
v___y_3383_ = v_a_3413_;
v___y_3384_ = v___x_3411_;
v___y_3385_ = v___y_3409_;
v___y_3386_ = v___x_3415_;
goto v___jp_3370_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
lean_dec(v___y_3403_);
v_a_3416_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3417_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3371_ = v___y_3398_;
v___y_3372_ = v___y_3399_;
v___y_3373_ = v___y_3397_;
v___y_3374_ = v___y_3400_;
v___y_3375_ = v___y_3401_;
v___y_3376_ = v___y_3402_;
v___y_3377_ = v___y_3404_;
v___y_3378_ = v___y_3405_;
v___y_3379_ = v___y_3406_;
v___y_3380_ = v___y_3410_;
v___y_3381_ = v___y_3407_;
v___y_3382_ = v___y_3408_;
v___y_3383_ = v_a_3416_;
v___y_3384_ = v___x_3411_;
v___y_3385_ = v___y_3409_;
v___y_3386_ = v___x_3417_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v___y_3410_);
lean_dec(v___y_3408_);
lean_dec(v___y_3403_);
lean_dec(v___y_3400_);
lean_dec(v___y_3397_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v_a_3418_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3412_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3412_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
v___jp_3426_:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Syntax_getOptional_x3f(v___y_3427_);
lean_dec(v___y_3427_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
v___y_3397_ = v___y_3429_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3436_;
v___y_3400_ = v___y_3430_;
v___y_3401_ = v___y_3434_;
v___y_3402_ = v___y_3431_;
v___y_3403_ = v_args_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3439_;
v___y_3406_ = v___y_3440_;
v___y_3407_ = v___y_3435_;
v___y_3408_ = v___y_3428_;
v___y_3409_ = v___y_3437_;
v___y_3410_ = v___x_3442_;
goto v___jp_3396_;
}
else
{
lean_object* v_val_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_val_3443_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3441_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_val_3443_);
lean_dec(v___x_3441_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_val_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
v___y_3397_ = v___y_3429_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3436_;
v___y_3400_ = v___y_3430_;
v___y_3401_ = v___y_3434_;
v___y_3402_ = v___y_3431_;
v___y_3403_ = v_args_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3439_;
v___y_3406_ = v___y_3440_;
v___y_3407_ = v___y_3435_;
v___y_3408_ = v___y_3428_;
v___y_3409_ = v___y_3437_;
v___y_3410_ = v___x_3448_;
goto v___jp_3396_;
}
}
}
}
v___jp_3452_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3467_ = lean_unsigned_to_nat(3u);
v___x_3468_ = l_Lean_Syntax_getArg(v___y_3457_, v___x_3467_);
lean_dec(v___y_3457_);
v___x_3469_ = l_Lean_Syntax_isNone(v___x_3468_);
if (v___x_3469_ == 0)
{
uint8_t v___x_3470_; 
lean_inc(v___x_3468_);
v___x_3470_ = l_Lean_Syntax_matchesNull(v___x_3468_, v___x_3451_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v___x_3468_);
lean_dec(v_o_3458_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3472_ = l_Lean_Syntax_getArg(v___x_3468_, v___x_2520_);
lean_dec(v___x_3468_);
v___x_3473_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3474_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3473_);
lean_inc(v___x_3472_);
v___x_3475_ = l_Lean_Syntax_isOfKind(v___x_3472_, v___x_3474_);
lean_dec(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec(v___x_3472_);
lean_dec(v_o_3458_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3476_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v_args_3478_; lean_object* v___x_3479_; 
v___x_3477_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3451_);
lean_dec(v___x_3472_);
v_args_3478_ = l_Lean_Syntax_getArgs(v___x_3477_);
lean_dec(v___x_3477_);
v___x_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_args_3478_);
v___y_3427_ = v___y_3455_;
v___y_3428_ = v___y_3454_;
v___y_3429_ = v___y_3453_;
v___y_3430_ = v_o_3458_;
v___y_3431_ = v___y_3456_;
v_args_3432_ = v___x_3479_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3460_;
v___y_3435_ = v___y_3461_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
goto v___jp_3426_;
}
}
}
else
{
lean_object* v___x_3480_; 
lean_dec(v___x_3468_);
v___x_3480_ = lean_box(0);
v___y_3427_ = v___y_3455_;
v___y_3428_ = v___y_3454_;
v___y_3429_ = v___y_3453_;
v___y_3430_ = v_o_3458_;
v___y_3431_ = v___y_3456_;
v_args_3432_ = v___x_3480_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3460_;
v___y_3435_ = v___y_3461_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
goto v___jp_3426_;
}
}
v___jp_3481_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3491_ = lean_unsigned_to_nat(2u);
v___x_3492_ = l_Lean_Syntax_getArg(v_stx_2504_, v___x_3491_);
v___x_3493_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3494_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3493_);
lean_inc(v___x_3492_);
v___x_3495_ = l_Lean_Syntax_isOfKind(v___x_3492_, v___x_3494_);
lean_dec(v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
lean_dec(v___x_3492_);
lean_dec(v_bang_3482_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3496_;
}
else
{
lean_object* v_cfg_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_cfg_3497_ = l_Lean_Syntax_getArg(v___x_3492_, v___x_2520_);
v___x_3498_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
lean_inc_ref(v___x_2506_);
v___x_3499_ = l_Lean_Name_mkStr4(v___x_2506_, v___x_2507_, v___x_2508_, v___x_3498_);
lean_inc(v_cfg_3497_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v_cfg_3497_, v___x_3499_);
lean_dec(v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_cfg_3497_);
lean_dec(v___x_3492_);
lean_dec(v_bang_3482_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3502_ = l_Lean_Syntax_getArg(v___x_3492_, v___x_3451_);
v___x_3503_ = l_Lean_Syntax_getArg(v___x_3492_, v___x_3491_);
v___x_3504_ = l_Lean_Syntax_isNone(v___x_3503_);
if (v___x_3504_ == 0)
{
uint8_t v___x_3505_; 
lean_inc(v___x_3503_);
v___x_3505_ = l_Lean_Syntax_matchesNull(v___x_3503_, v___x_3451_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v___x_3503_);
lean_dec(v___x_3502_);
lean_dec(v_cfg_3497_);
lean_dec(v___x_3492_);
lean_dec(v_bang_3482_);
lean_dec(v_tk_2521_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v___x_2506_);
v___x_3506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3506_;
}
else
{
lean_object* v_o_3507_; lean_object* v___x_3508_; 
v_o_3507_ = l_Lean_Syntax_getArg(v___x_3503_, v___x_2520_);
lean_dec(v___x_3503_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_o_3507_);
v___y_3453_ = v_cfg_3497_;
v___y_3454_ = v_bang_3482_;
v___y_3455_ = v___x_3502_;
v___y_3456_ = v___x_3495_;
v___y_3457_ = v___x_3492_;
v_o_3458_ = v___x_3508_;
v___y_3459_ = v___y_3483_;
v___y_3460_ = v___y_3484_;
v___y_3461_ = v___y_3485_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___y_3487_;
v___y_3464_ = v___y_3488_;
v___y_3465_ = v___y_3489_;
v___y_3466_ = v___y_3490_;
goto v___jp_3452_;
}
}
else
{
lean_object* v___x_3509_; 
lean_dec(v___x_3503_);
v___x_3509_ = lean_box(0);
v___y_3453_ = v_cfg_3497_;
v___y_3454_ = v_bang_3482_;
v___y_3455_ = v___x_3502_;
v___y_3456_ = v___x_3495_;
v___y_3457_ = v___x_3492_;
v_o_3458_ = v___x_3509_;
v___y_3459_ = v___y_3483_;
v___y_3460_ = v___y_3484_;
v___y_3461_ = v___y_3485_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___y_3487_;
v___y_3464_ = v___y_3488_;
v___y_3465_ = v___y_3489_;
v___y_3466_ = v___y_3490_;
goto v___jp_3452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3517_, lean_object* v_stx_3518_, lean_object* v___x_3519_, lean_object* v___x_3520_, lean_object* v___x_3521_, lean_object* v___x_3522_, lean_object* v___f_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
uint8_t v___x_31003__boxed_3533_; uint8_t v___x_31004__boxed_3534_; lean_object* v_res_3535_; 
v___x_31003__boxed_3533_ = lean_unbox(v___x_3517_);
v___x_31004__boxed_3534_ = lean_unbox(v___x_3519_);
v_res_3535_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31003__boxed_3533_, v_stx_3518_, v___x_31004__boxed_3534_, v___x_3520_, v___x_3521_, v___x_3522_, v___f_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v_stx_3518_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; uint8_t v___x_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___y_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3555_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3542_);
v___x_3556_ = l_Lean_Syntax_isOfKind(v_stx_3542_, v___x_3555_);
v___x_3557_ = 1;
v___f_3558_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3559_ = lean_box(v___x_3556_);
v___x_3560_ = lean_box(v___x_3557_);
v___y_3561_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3561_, 0, v___x_3559_);
lean_closure_set(v___y_3561_, 1, v_stx_3542_);
lean_closure_set(v___y_3561_, 2, v___x_3560_);
lean_closure_set(v___y_3561_, 3, v___x_3552_);
lean_closure_set(v___y_3561_, 4, v___x_3553_);
lean_closure_set(v___y_3561_, 5, v___x_3554_);
lean_closure_set(v___y_3561_, 6, v___f_3558_);
v___x_3562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3562_, 0, v___y_3561_);
v___x_3563_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3562_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3575_, lean_object* v_as_3576_, lean_object* v_as_x27_3577_, lean_object* v_b_3578_, lean_object* v_a_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3575_, v_as_x27_3577_, v_b_3578_, v___y_3586_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3590_, lean_object* v_as_3591_, lean_object* v_as_x27_3592_, lean_object* v_b_3593_, lean_object* v_a_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3590_, v_as_3591_, v_as_x27_3592_, v_b_3593_, v_a_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v_as_x27_3592_);
lean_dec(v_as_3591_);
lean_dec(v___x_3590_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3612_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3613_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3616_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3612_, v___x_3613_, v___x_3614_, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3646_ = l_Lean_addBuiltinDeclarationRanges(v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3649_, lean_object* v_simprocs_3650_, lean_object* v_fvarIdsToSimp_3651_, uint8_t v_simplifyTarget_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = lean_unsigned_to_nat(32u);
v___x_3662_ = lean_mk_empty_array_with_capacity(v___x_3661_);
lean_dec_ref(v___x_3662_);
v___x_3663_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3664_ = l_Lean_Meta_dsimpGoal(v_a_3660_, v_ctx_3649_, v_simprocs_3650_, v_simplifyTarget_3652_, v_fvarIdsToSimp_3651_, v___x_3663_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v_fst_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v_fst_3666_ = lean_ctor_get(v_a_3665_, 0);
if (lean_obj_tag(v_fst_3666_) == 0)
{
lean_object* v_snd_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_snd_3667_ = lean_ctor_get(v_a_3665_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_a_3665_);
v___x_3668_ = lean_box(0);
v___x_3669_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3668_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v___x_3669_, 0);
lean_dec(v_unused_3677_);
v___x_3671_ = v___x_3669_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_dec(v___x_3669_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v_snd_3667_);
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_snd_3667_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_snd_3667_);
v_a_3678_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3669_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3669_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_snd_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3712_; 
lean_inc_ref(v_fst_3666_);
v_snd_3686_ = lean_ctor_get(v_a_3665_, 1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v_a_3665_, 0);
lean_dec(v_unused_3713_);
v___x_3688_ = v_a_3665_;
v_isShared_3689_ = v_isSharedCheck_3712_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_snd_3686_);
lean_dec(v_a_3665_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3712_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v_val_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v_val_3690_ = lean_ctor_get(v_fst_3666_, 0);
lean_inc(v_val_3690_);
lean_dec_ref_known(v_fst_3666_, 1);
v___x_3691_ = lean_box(0);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 1);
lean_ctor_set(v___x_3688_, 1, v___x_3691_);
lean_ctor_set(v___x_3688_, 0, v_val_3690_);
v___x_3693_ = v___x_3688_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_val_3690_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3693_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3694_, 0);
lean_dec(v_unused_3702_);
v___x_3696_ = v___x_3694_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v___x_3694_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_snd_3686_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_snd_3686_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_snd_3686_);
v_a_3703_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3694_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3694_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
v_a_3714_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3664_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3664_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_fvarIdsToSimp_3651_);
lean_dec_ref(v_simprocs_3650_);
lean_dec_ref(v_ctx_3649_);
v_a_3722_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3659_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3659_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3730_, lean_object* v_simprocs_3731_, lean_object* v_fvarIdsToSimp_3732_, lean_object* v_simplifyTarget_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
uint8_t v_simplifyTarget_boxed_3740_; lean_object* v_res_3741_; 
v_simplifyTarget_boxed_3740_ = lean_unbox(v_simplifyTarget_3733_);
v_res_3741_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3730_, v_simprocs_3731_, v_fvarIdsToSimp_3732_, v_simplifyTarget_boxed_3740_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3742_, lean_object* v_simprocs_3743_, lean_object* v_fvarIdsToSimp_3744_, uint8_t v_simplifyTarget_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3742_, v_simprocs_3743_, v_fvarIdsToSimp_3744_, v_simplifyTarget_3745_, v_a_3747_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3756_, lean_object* v_simprocs_3757_, lean_object* v_fvarIdsToSimp_3758_, lean_object* v_simplifyTarget_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
uint8_t v_simplifyTarget_boxed_3769_; lean_object* v_res_3770_; 
v_simplifyTarget_boxed_3769_ = lean_unbox(v_simplifyTarget_3759_);
v_res_3770_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3756_, v_simprocs_3757_, v_fvarIdsToSimp_3758_, v_simplifyTarget_boxed_3769_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3771_, lean_object* v_simprocs_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3774_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3784_ = l_Lean_MVarId_getNondepPropHyps(v_a_3783_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; uint8_t v___x_3786_; lean_object* v___x_3787_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v___x_3786_ = 1;
v___x_3787_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3771_, v_simprocs_3772_, v_a_3785_, v___x_3786_, v___y_3774_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3787_;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_simprocs_3772_);
lean_dec_ref(v_ctx_3771_);
v_a_3788_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3784_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3784_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v_simprocs_3772_);
lean_dec_ref(v_ctx_3771_);
v_a_3796_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3782_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3782_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3804_, lean_object* v_simprocs_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3804_, v_simprocs_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3816_, lean_object* v_ctx_3817_, lean_object* v_simprocs_3818_, uint8_t v_type_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3816_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3829_, 1);
v___x_3831_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3817_, v_simprocs_3818_, v_a_3830_, v_type_3819_, v___y_3821_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v_simprocs_3818_);
lean_dec_ref(v_ctx_3817_);
v_a_3832_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3829_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3829_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3840_, lean_object* v_ctx_3841_, lean_object* v_simprocs_3842_, lean_object* v_type_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
uint8_t v_type_633__boxed_3853_; lean_object* v_res_3854_; 
v_type_633__boxed_3853_ = lean_unbox(v_type_3843_);
v_res_3854_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3840_, v_ctx_3841_, v_simprocs_3842_, v_type_633__boxed_3853_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3855_, lean_object* v_simprocs_3856_, lean_object* v_loc_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
if (lean_obj_tag(v_loc_3857_) == 0)
{
lean_object* v___f_3867_; lean_object* v___x_3868_; 
v___f_3867_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3867_, 0, v_ctx_3855_);
lean_closure_set(v___f_3867_, 1, v_simprocs_3856_);
v___x_3868_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3867_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
return v___x_3868_;
}
else
{
lean_object* v_hypotheses_3869_; uint8_t v_type_3870_; lean_object* v___x_3871_; lean_object* v___f_3872_; lean_object* v___x_3873_; 
v_hypotheses_3869_ = lean_ctor_get(v_loc_3857_, 0);
lean_inc_ref(v_hypotheses_3869_);
v_type_3870_ = lean_ctor_get_uint8(v_loc_3857_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3857_, 1);
v___x_3871_ = lean_box(v_type_3870_);
v___f_3872_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3872_, 0, v_hypotheses_3869_);
lean_closure_set(v___f_3872_, 1, v_ctx_3855_);
lean_closure_set(v___f_3872_, 2, v_simprocs_3856_);
lean_closure_set(v___f_3872_, 3, v___x_3871_);
v___x_3873_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3872_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
return v___x_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3874_, lean_object* v_simprocs_3875_, lean_object* v_loc_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3874_, v_simprocs_3875_, v_loc_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3891_, lean_object* v_stx_3892_, uint8_t v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
if (v___x_3891_ == 0)
{
lean_object* v___x_3906_; 
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_3906_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3906_;
}
else
{
lean_object* v___x_3907_; lean_object* v_tk_3908_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; uint8_t v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v_stx_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; uint8_t v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; uint8_t v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; uint8_t v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; uint8_t v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; uint8_t v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; uint8_t v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; uint8_t v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v_args_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___x_4289_; uint8_t v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v_o_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v_bang_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_3907_ = lean_unsigned_to_nat(0u);
v_tk_3908_ = l_Lean_Syntax_getArg(v_stx_3892_, v___x_3907_);
v___x_4289_ = lean_unsigned_to_nat(1u);
v___x_4346_ = l_Lean_Syntax_getArg(v_stx_3892_, v___x_4289_);
v___x_4347_ = l_Lean_Syntax_isNone(v___x_4346_);
if (v___x_4347_ == 0)
{
uint8_t v___x_4348_; 
lean_inc(v___x_4346_);
v___x_4348_ = l_Lean_Syntax_matchesNull(v___x_4346_, v___x_4289_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec(v___x_4346_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4349_;
}
else
{
lean_object* v_bang_4350_; lean_object* v___x_4351_; 
v_bang_4350_ = l_Lean_Syntax_getArg(v___x_4346_, v___x_3907_);
lean_dec(v___x_4346_);
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_bang_4350_);
v_bang_4319_ = v___x_4351_;
v___y_4320_ = v___y_3897_;
v___y_4321_ = v___y_3898_;
v___y_4322_ = v___y_3899_;
v___y_4323_ = v___y_3900_;
v___y_4324_ = v___y_3901_;
v___y_4325_ = v___y_3902_;
v___y_4326_ = v___y_3903_;
v___y_4327_ = v___y_3904_;
goto v___jp_4318_;
}
}
else
{
lean_object* v___x_4352_; 
lean_dec(v___x_4346_);
v___x_4352_ = lean_box(0);
v_bang_4319_ = v___x_4352_;
v___y_4320_ = v___y_3897_;
v___y_4321_ = v___y_3898_;
v___y_4322_ = v___y_3899_;
v___y_4323_ = v___y_3900_;
v___y_4324_ = v___y_3901_;
v___y_4325_ = v___y_3902_;
v___y_4326_ = v___y_3903_;
v___y_4327_ = v___y_3904_;
goto v___jp_4318_;
}
v___jp_3909_:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3918_, v___y_3912_, v___y_3921_, v___y_3911_, v___y_3917_, v___y_3916_, v___y_3920_, v___y_3910_, v___y_3915_, v___y_3913_, v___y_3914_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v_usedTheorems_3924_; lean_object* v_diag_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3967_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v_usedTheorems_3924_ = lean_ctor_get(v_a_3923_, 0);
v_diag_3925_ = lean_ctor_get(v_a_3923_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_a_3923_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3927_ = v_a_3923_;
v_isShared_3928_ = v_isSharedCheck_3967_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_diag_3925_);
lean_inc(v_usedTheorems_3924_);
lean_dec(v_a_3923_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3967_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3919_, v_usedTheorems_3924_, v___y_3910_, v___y_3915_, v___y_3913_, v___y_3914_);
lean_dec_ref(v_usedTheorems_3924_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v_ref_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v_ref_3931_ = lean_ctor_get(v___y_3913_, 4);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v_a_3930_);
lean_ctor_set(v___x_3927_, 0, v___x_3932_);
v___x_3934_ = v___x_3927_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_a_3930_);
v___x_3934_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3935_ = lean_box(0);
v___x_3936_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
lean_ctor_set(v___x_3936_, 2, v___x_3935_);
lean_ctor_set(v___x_3936_, 3, v___x_3935_);
lean_ctor_set(v___x_3936_, 4, v___x_3935_);
lean_ctor_set(v___x_3936_, 5, v___x_3935_);
lean_inc(v_ref_3931_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_ref_3931_);
v___x_3938_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3939_ = 4;
v___x_3940_ = l_Lean_MessageData_nil;
v___x_3941_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3908_, v___x_3936_, v___x_3937_, v___x_3938_, v___x_3935_, v___x_3939_, v___x_3940_, v___y_3913_, v___y_3914_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; 
v_unused_3949_ = lean_ctor_get(v___x_3941_, 0);
lean_dec(v_unused_3949_);
v___x_3943_ = v___x_3941_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_dec(v___x_3941_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v_diag_3925_);
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_diag_3925_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec_ref(v_diag_3925_);
v_a_3950_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3941_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3941_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_del_object(v___x_3927_);
lean_dec_ref(v_diag_3925_);
lean_dec(v_tk_3908_);
v_a_3959_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3929_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3929_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v___y_3919_);
lean_dec(v_tk_3908_);
v_a_3968_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3922_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3922_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
v___jp_3976_:
{
if (lean_obj_tag(v___y_3986_) == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3990_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
lean_ctor_set_uint8(v___x_3990_, sizeof(void*)*1, v___x_3893_);
v___y_3910_ = v___y_3979_;
v___y_3911_ = v___y_3978_;
v___y_3912_ = v___y_3977_;
v___y_3913_ = v___y_3980_;
v___y_3914_ = v___y_3982_;
v___y_3915_ = v___y_3981_;
v___y_3916_ = v___y_3983_;
v___y_3917_ = v___y_3984_;
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3985_;
v___y_3920_ = v___y_3987_;
v___y_3921_ = v___x_3990_;
goto v___jp_3909_;
}
else
{
lean_object* v_val_3991_; lean_object* v___x_3992_; 
v_val_3991_ = lean_ctor_get(v___y_3986_, 0);
lean_inc(v_val_3991_);
lean_dec_ref_known(v___y_3986_, 1);
v___x_3992_ = l_Lean_Elab_Tactic_expandLocation(v_val_3991_);
lean_dec(v_val_3991_);
v___y_3910_ = v___y_3979_;
v___y_3911_ = v___y_3978_;
v___y_3912_ = v___y_3977_;
v___y_3913_ = v___y_3980_;
v___y_3914_ = v___y_3982_;
v___y_3915_ = v___y_3981_;
v___y_3916_ = v___y_3983_;
v___y_3917_ = v___y_3984_;
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3985_;
v___y_3920_ = v___y_3987_;
v___y_3921_ = v___x_3992_;
goto v___jp_3909_;
}
}
v___jp_3993_:
{
uint8_t v___x_4006_; uint8_t v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4006_ = 0;
v___x_4007_ = 2;
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4009_ = lean_box(v___x_4006_);
v___x_4010_ = lean_box(v___x_4007_);
v___x_4011_ = lean_box(v___x_4006_);
lean_inc(v_stx_3997_);
v___x_4012_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4012_, 0, v_stx_3997_);
lean_closure_set(v___x_4012_, 1, v___x_4009_);
lean_closure_set(v___x_4012_, 2, v___x_4010_);
lean_closure_set(v___x_4012_, 3, v___x_4011_);
lean_closure_set(v___x_4012_, 4, v___x_4008_);
v___x_4013_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4012_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
if (lean_obj_tag(v___y_3996_) == 0)
{
lean_object* v_ctx_4015_; lean_object* v_simprocs_4016_; 
v_ctx_4015_ = lean_ctor_get(v_a_4014_, 0);
lean_inc_ref(v_ctx_4015_);
v_simprocs_4016_ = lean_ctor_get(v_a_4014_, 1);
lean_inc_ref(v_simprocs_4016_);
lean_dec(v_a_4014_);
v___y_3977_ = v_simprocs_4016_;
v___y_3978_ = v___y_3998_;
v___y_3979_ = v___y_4002_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4005_;
v___y_3983_ = v___y_4000_;
v___y_3984_ = v___y_3999_;
v___y_3985_ = v_stx_3997_;
v___y_3986_ = v___y_3995_;
v___y_3987_ = v___y_4001_;
v___y_3988_ = v_ctx_4015_;
goto v___jp_3976_;
}
else
{
lean_dec_ref_known(v___y_3996_, 1);
if (v___y_3994_ == 0)
{
lean_object* v_ctx_4017_; lean_object* v_simprocs_4018_; 
v_ctx_4017_ = lean_ctor_get(v_a_4014_, 0);
lean_inc_ref(v_ctx_4017_);
v_simprocs_4018_ = lean_ctor_get(v_a_4014_, 1);
lean_inc_ref(v_simprocs_4018_);
lean_dec(v_a_4014_);
v___y_3977_ = v_simprocs_4018_;
v___y_3978_ = v___y_3998_;
v___y_3979_ = v___y_4002_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4005_;
v___y_3983_ = v___y_4000_;
v___y_3984_ = v___y_3999_;
v___y_3985_ = v_stx_3997_;
v___y_3986_ = v___y_3995_;
v___y_3987_ = v___y_4001_;
v___y_3988_ = v_ctx_4017_;
goto v___jp_3976_;
}
else
{
lean_object* v_ctx_4019_; lean_object* v_simprocs_4020_; lean_object* v___x_4021_; 
v_ctx_4019_ = lean_ctor_get(v_a_4014_, 0);
lean_inc_ref(v_ctx_4019_);
v_simprocs_4020_ = lean_ctor_get(v_a_4014_, 1);
lean_inc_ref(v_simprocs_4020_);
lean_dec(v_a_4014_);
v___x_4021_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4019_);
v___y_3977_ = v_simprocs_4020_;
v___y_3978_ = v___y_3998_;
v___y_3979_ = v___y_4002_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4005_;
v___y_3983_ = v___y_4000_;
v___y_3984_ = v___y_3999_;
v___y_3985_ = v_stx_3997_;
v___y_3986_ = v___y_3995_;
v___y_3987_ = v___y_4001_;
v___y_3988_ = v___x_4021_;
goto v___jp_3976_;
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v_stx_3997_);
lean_dec(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec(v_tk_3908_);
v_a_4022_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4013_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4013_);
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
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_inc_ref(v___y_4050_);
v___x_4052_ = l_Array_append___redArg(v___y_4050_, v___y_4051_);
lean_dec_ref(v___y_4051_);
lean_inc(v___y_4038_);
lean_inc(v___y_4043_);
v___x_4053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4053_, 0, v___y_4043_);
lean_ctor_set(v___x_4053_, 1, v___y_4038_);
lean_ctor_set(v___x_4053_, 2, v___x_4052_);
v___x_4054_ = l_Lean_Syntax_node6(v___y_4043_, v___y_4035_, v___y_4049_, v___y_4044_, v___y_4031_, v___y_4032_, v___y_4048_, v___x_4053_);
v___y_3994_ = v___y_4040_;
v___y_3995_ = v___y_4047_;
v___y_3996_ = v___y_4037_;
v_stx_3997_ = v___x_4054_;
v___y_3998_ = v___y_4034_;
v___y_3999_ = v___y_4045_;
v___y_4000_ = v___y_4041_;
v___y_4001_ = v___y_4042_;
v___y_4002_ = v___y_4046_;
v___y_4003_ = v___y_4039_;
v___y_4004_ = v___y_4036_;
v___y_4005_ = v___y_4033_;
goto v___jp_3993_;
}
v___jp_4055_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_inc_ref(v___y_4074_);
v___x_4076_ = l_Array_append___redArg(v___y_4074_, v___y_4075_);
lean_dec_ref(v___y_4075_);
lean_inc(v___y_4062_);
lean_inc(v___y_4068_);
v___x_4077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4077_, 0, v___y_4068_);
lean_ctor_set(v___x_4077_, 1, v___y_4062_);
lean_ctor_set(v___x_4077_, 2, v___x_4076_);
if (lean_obj_tag(v___y_4072_) == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4063_;
v___y_4038_ = v___y_4062_;
v___y_4039_ = v___y_4064_;
v___y_4040_ = v___y_4067_;
v___y_4041_ = v___y_4066_;
v___y_4042_ = v___y_4065_;
v___y_4043_ = v___y_4068_;
v___y_4044_ = v___y_4069_;
v___y_4045_ = v___y_4070_;
v___y_4046_ = v___y_4071_;
v___y_4047_ = v___y_4072_;
v___y_4048_ = v___x_4077_;
v___y_4049_ = v___y_4073_;
v___y_4050_ = v___y_4074_;
v___y_4051_ = v___x_4078_;
goto v___jp_4030_;
}
else
{
lean_object* v_val_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_val_4079_ = lean_ctor_get(v___y_4072_, 0);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4079_);
v___x_4081_ = lean_array_push(v___x_4080_, v_val_4079_);
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4063_;
v___y_4038_ = v___y_4062_;
v___y_4039_ = v___y_4064_;
v___y_4040_ = v___y_4067_;
v___y_4041_ = v___y_4066_;
v___y_4042_ = v___y_4065_;
v___y_4043_ = v___y_4068_;
v___y_4044_ = v___y_4069_;
v___y_4045_ = v___y_4070_;
v___y_4046_ = v___y_4071_;
v___y_4047_ = v___y_4072_;
v___y_4048_ = v___x_4077_;
v___y_4049_ = v___y_4073_;
v___y_4050_ = v___y_4074_;
v___y_4051_ = v___x_4081_;
goto v___jp_4030_;
}
}
v___jp_4082_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_inc_ref(v___y_4101_);
v___x_4103_ = l_Array_append___redArg(v___y_4101_, v___y_4102_);
lean_dec_ref(v___y_4102_);
lean_inc(v___y_4088_);
lean_inc(v___y_4094_);
v___x_4104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4104_, 0, v___y_4094_);
lean_ctor_set(v___x_4104_, 1, v___y_4088_);
lean_ctor_set(v___x_4104_, 2, v___x_4103_);
if (lean_obj_tag(v___y_4100_) == 1)
{
lean_object* v_val_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_val_4105_ = lean_ctor_get(v___y_4100_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v___y_4100_, 1);
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4094_, 3);
v___x_4107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___y_4094_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
lean_inc_ref(v___y_4101_);
v___x_4108_ = l_Array_append___redArg(v___y_4101_, v_val_4105_);
lean_dec(v_val_4105_);
lean_inc(v___y_4088_);
v___x_4109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4109_, 0, v___y_4094_);
lean_ctor_set(v___x_4109_, 1, v___y_4088_);
lean_ctor_set(v___x_4109_, 2, v___x_4108_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___y_4094_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = l_Array_mkArray3___redArg(v___x_4107_, v___x_4109_, v___x_4111_);
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___x_4104_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4087_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4092_;
v___y_4066_ = v___y_4093_;
v___y_4067_ = v___y_4091_;
v___y_4068_ = v___y_4094_;
v___y_4069_ = v___y_4095_;
v___y_4070_ = v___y_4096_;
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4098_;
v___y_4073_ = v___y_4099_;
v___y_4074_ = v___y_4101_;
v___y_4075_ = v___x_4112_;
goto v___jp_4055_;
}
else
{
lean_object* v___x_4113_; 
lean_dec(v___y_4100_);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___x_4104_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4087_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4092_;
v___y_4066_ = v___y_4093_;
v___y_4067_ = v___y_4091_;
v___y_4068_ = v___y_4094_;
v___y_4069_ = v___y_4095_;
v___y_4070_ = v___y_4096_;
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4098_;
v___y_4073_ = v___y_4099_;
v___y_4074_ = v___y_4101_;
v___y_4075_ = v___x_4113_;
goto v___jp_4055_;
}
}
v___jp_4114_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_inc_ref(v___y_4126_);
v___x_4136_ = l_Array_append___redArg(v___y_4126_, v___y_4135_);
lean_dec_ref(v___y_4135_);
lean_inc(v___y_4134_);
lean_inc(v___y_4119_);
v___x_4137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4137_, 0, v___y_4119_);
lean_ctor_set(v___x_4137_, 1, v___y_4134_);
lean_ctor_set(v___x_4137_, 2, v___x_4136_);
v___x_4138_ = l_Lean_Syntax_node6(v___y_4119_, v___y_4129_, v___y_4117_, v___y_4127_, v___y_4118_, v___y_4133_, v___y_4128_, v___x_4137_);
v___y_3994_ = v___y_4123_;
v___y_3995_ = v___y_4132_;
v___y_3996_ = v___y_4121_;
v_stx_3997_ = v___x_4138_;
v___y_3998_ = v___y_4116_;
v___y_3999_ = v___y_4130_;
v___y_4000_ = v___y_4124_;
v___y_4001_ = v___y_4125_;
v___y_4002_ = v___y_4131_;
v___y_4003_ = v___y_4122_;
v___y_4004_ = v___y_4120_;
v___y_4005_ = v___y_4115_;
goto v___jp_3993_;
}
v___jp_4139_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_inc_ref(v___y_4151_);
v___x_4160_ = l_Array_append___redArg(v___y_4151_, v___y_4159_);
lean_dec_ref(v___y_4159_);
lean_inc(v___y_4158_);
lean_inc(v___y_4144_);
v___x_4161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4161_, 0, v___y_4144_);
lean_ctor_set(v___x_4161_, 1, v___y_4158_);
lean_ctor_set(v___x_4161_, 2, v___x_4160_);
if (lean_obj_tag(v___y_4156_) == 0)
{
lean_object* v___x_4162_; 
v___x_4162_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4142_;
v___y_4118_ = v___y_4143_;
v___y_4119_ = v___y_4144_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4149_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4151_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v___x_4161_;
v___y_4129_ = v___y_4154_;
v___y_4130_ = v___y_4153_;
v___y_4131_ = v___y_4155_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___y_4157_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___x_4162_;
goto v___jp_4114_;
}
else
{
lean_object* v_val_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_val_4163_ = lean_ctor_get(v___y_4156_, 0);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4163_);
v___x_4165_ = lean_array_push(v___x_4164_, v_val_4163_);
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4142_;
v___y_4118_ = v___y_4143_;
v___y_4119_ = v___y_4144_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4149_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4151_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v___x_4161_;
v___y_4129_ = v___y_4154_;
v___y_4130_ = v___y_4153_;
v___y_4131_ = v___y_4155_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___y_4157_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___x_4165_;
goto v___jp_4114_;
}
}
v___jp_4166_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_inc_ref(v___y_4178_);
v___x_4187_ = l_Array_append___redArg(v___y_4178_, v___y_4186_);
lean_dec_ref(v___y_4186_);
lean_inc(v___y_4184_);
lean_inc(v___y_4171_);
v___x_4188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4188_, 0, v___y_4171_);
lean_ctor_set(v___x_4188_, 1, v___y_4184_);
lean_ctor_set(v___x_4188_, 2, v___x_4187_);
if (lean_obj_tag(v___y_4185_) == 1)
{
lean_object* v_val_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v_val_4189_ = lean_ctor_get(v___y_4185_, 0);
lean_inc(v_val_4189_);
lean_dec_ref_known(v___y_4185_, 1);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4171_, 3);
v___x_4191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___y_4171_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
lean_inc_ref(v___y_4178_);
v___x_4192_ = l_Array_append___redArg(v___y_4178_, v_val_4189_);
lean_dec(v_val_4189_);
lean_inc(v___y_4184_);
v___x_4193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4193_, 0, v___y_4171_);
lean_ctor_set(v___x_4193_, 1, v___y_4184_);
lean_ctor_set(v___x_4193_, 2, v___x_4192_);
v___x_4194_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___y_4171_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = l_Array_mkArray3___redArg(v___x_4191_, v___x_4193_, v___x_4195_);
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4174_;
v___y_4148_ = v___y_4176_;
v___y_4149_ = v___y_4177_;
v___y_4150_ = v___y_4175_;
v___y_4151_ = v___y_4178_;
v___y_4152_ = v___y_4179_;
v___y_4153_ = v___y_4181_;
v___y_4154_ = v___y_4180_;
v___y_4155_ = v___y_4182_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___x_4188_;
v___y_4158_ = v___y_4184_;
v___y_4159_ = v___x_4196_;
goto v___jp_4139_;
}
else
{
lean_object* v___x_4197_; 
lean_dec(v___y_4185_);
v___x_4197_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4174_;
v___y_4148_ = v___y_4176_;
v___y_4149_ = v___y_4177_;
v___y_4150_ = v___y_4175_;
v___y_4151_ = v___y_4178_;
v___y_4152_ = v___y_4179_;
v___y_4153_ = v___y_4181_;
v___y_4154_ = v___y_4180_;
v___y_4155_ = v___y_4182_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___x_4188_;
v___y_4158_ = v___y_4184_;
v___y_4159_ = v___x_4197_;
goto v___jp_4139_;
}
}
v___jp_4198_:
{
lean_object* v_ref_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_ref_4214_ = lean_ctor_get(v___y_4202_, 4);
v___x_4215_ = l_Lean_SourceInfo_fromRef(v_ref_4214_, v___y_4213_);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4217_ = l_Lean_Name_mkStr4(v___x_3894_, v___x_3895_, v___x_3896_, v___x_4216_);
v___x_4218_ = l_Lean_SourceInfo_fromRef(v_tk_3908_, v___x_3893_);
v___x_4219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4218_);
lean_ctor_set(v___x_4219_, 1, v___x_4216_);
v___x_4220_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4221_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4215_);
v___x_4222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4215_);
lean_ctor_set(v___x_4222_, 1, v___x_4220_);
lean_ctor_set(v___x_4222_, 2, v___x_4221_);
if (lean_obj_tag(v___y_4199_) == 1)
{
lean_object* v_val_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_val_4223_ = lean_ctor_get(v___y_4199_, 0);
lean_inc(v_val_4223_);
lean_dec_ref_known(v___y_4199_, 1);
v___x_4224_ = l_Lean_SourceInfo_fromRef(v_val_4223_, v___x_3893_);
lean_dec(v_val_4223_);
v___x_4225_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4224_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l_Array_mkArray1___redArg(v___x_4226_);
v___y_4083_ = v___x_4222_;
v___y_4084_ = v___y_4200_;
v___y_4085_ = v___y_4201_;
v___y_4086_ = v___x_4217_;
v___y_4087_ = v___y_4202_;
v___y_4088_ = v___x_4220_;
v___y_4089_ = v___y_4203_;
v___y_4090_ = v___y_4204_;
v___y_4091_ = v___y_4205_;
v___y_4092_ = v___y_4206_;
v___y_4093_ = v___y_4207_;
v___y_4094_ = v___x_4215_;
v___y_4095_ = v___y_4208_;
v___y_4096_ = v___y_4209_;
v___y_4097_ = v___y_4210_;
v___y_4098_ = v___y_4211_;
v___y_4099_ = v___x_4219_;
v___y_4100_ = v___y_4212_;
v___y_4101_ = v___x_4221_;
v___y_4102_ = v___x_4227_;
goto v___jp_4082_;
}
else
{
lean_object* v___x_4228_; 
lean_dec(v___y_4199_);
v___x_4228_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4083_ = v___x_4222_;
v___y_4084_ = v___y_4200_;
v___y_4085_ = v___y_4201_;
v___y_4086_ = v___x_4217_;
v___y_4087_ = v___y_4202_;
v___y_4088_ = v___x_4220_;
v___y_4089_ = v___y_4203_;
v___y_4090_ = v___y_4204_;
v___y_4091_ = v___y_4205_;
v___y_4092_ = v___y_4206_;
v___y_4093_ = v___y_4207_;
v___y_4094_ = v___x_4215_;
v___y_4095_ = v___y_4208_;
v___y_4096_ = v___y_4209_;
v___y_4097_ = v___y_4210_;
v___y_4098_ = v___y_4211_;
v___y_4099_ = v___x_4219_;
v___y_4100_ = v___y_4212_;
v___y_4101_ = v___x_4221_;
v___y_4102_ = v___x_4228_;
goto v___jp_4082_;
}
}
v___jp_4229_:
{
if (lean_obj_tag(v___y_4234_) == 0)
{
uint8_t v___x_4244_; 
v___x_4244_ = 0;
v___y_4199_ = v___y_4230_;
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4236_;
v___y_4206_ = v___y_4237_;
v___y_4207_ = v___y_4238_;
v___y_4208_ = v___y_4239_;
v___y_4209_ = v___y_4240_;
v___y_4210_ = v___y_4241_;
v___y_4211_ = v___y_4243_;
v___y_4212_ = v___y_4242_;
v___y_4213_ = v___x_4244_;
goto v___jp_4198_;
}
else
{
if (v___y_4236_ == 0)
{
v___y_4199_ = v___y_4230_;
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4236_;
v___y_4206_ = v___y_4237_;
v___y_4207_ = v___y_4238_;
v___y_4208_ = v___y_4239_;
v___y_4209_ = v___y_4240_;
v___y_4210_ = v___y_4241_;
v___y_4211_ = v___y_4243_;
v___y_4212_ = v___y_4242_;
v___y_4213_ = v___y_4236_;
goto v___jp_4198_;
}
else
{
lean_object* v_ref_4245_; uint8_t v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_ref_4245_ = lean_ctor_get(v___y_4233_, 4);
v___x_4246_ = 0;
v___x_4247_ = l_Lean_SourceInfo_fromRef(v_ref_4245_, v___x_4246_);
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4249_ = l_Lean_Name_mkStr4(v___x_3894_, v___x_3895_, v___x_3896_, v___x_4248_);
v___x_4250_ = l_Lean_SourceInfo_fromRef(v_tk_3908_, v___x_3893_);
v___x_4251_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4254_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4247_);
v___x_4255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4247_);
lean_ctor_set(v___x_4255_, 1, v___x_4253_);
lean_ctor_set(v___x_4255_, 2, v___x_4254_);
if (lean_obj_tag(v___y_4230_) == 1)
{
lean_object* v_val_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_val_4256_ = lean_ctor_get(v___y_4230_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v___y_4230_, 1);
v___x_4257_ = l_Lean_SourceInfo_fromRef(v_val_4256_, v___x_3893_);
lean_dec(v_val_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Array_mkArray1___redArg(v___x_4259_);
v___y_4167_ = v___y_4231_;
v___y_4168_ = v___y_4232_;
v___y_4169_ = v___x_4252_;
v___y_4170_ = v___x_4255_;
v___y_4171_ = v___x_4247_;
v___y_4172_ = v___y_4233_;
v___y_4173_ = v___y_4234_;
v___y_4174_ = v___y_4235_;
v___y_4175_ = v___y_4238_;
v___y_4176_ = v___y_4237_;
v___y_4177_ = v___y_4236_;
v___y_4178_ = v___x_4254_;
v___y_4179_ = v___y_4239_;
v___y_4180_ = v___x_4249_;
v___y_4181_ = v___y_4240_;
v___y_4182_ = v___y_4241_;
v___y_4183_ = v___y_4243_;
v___y_4184_ = v___x_4253_;
v___y_4185_ = v___y_4242_;
v___y_4186_ = v___x_4260_;
goto v___jp_4166_;
}
else
{
lean_object* v___x_4261_; 
lean_dec(v___y_4230_);
v___x_4261_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4167_ = v___y_4231_;
v___y_4168_ = v___y_4232_;
v___y_4169_ = v___x_4252_;
v___y_4170_ = v___x_4255_;
v___y_4171_ = v___x_4247_;
v___y_4172_ = v___y_4233_;
v___y_4173_ = v___y_4234_;
v___y_4174_ = v___y_4235_;
v___y_4175_ = v___y_4238_;
v___y_4176_ = v___y_4237_;
v___y_4177_ = v___y_4236_;
v___y_4178_ = v___x_4254_;
v___y_4179_ = v___y_4239_;
v___y_4180_ = v___x_4249_;
v___y_4181_ = v___y_4240_;
v___y_4182_ = v___y_4241_;
v___y_4183_ = v___y_4243_;
v___y_4184_ = v___x_4253_;
v___y_4185_ = v___y_4242_;
v___y_4186_ = v___x_4261_;
goto v___jp_4166_;
}
}
}
}
v___jp_4262_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4277_ = lean_unsigned_to_nat(3u);
v___x_4278_ = l_Lean_Syntax_getArg(v___y_4266_, v___x_4277_);
lean_dec(v___y_4266_);
v___x_4279_ = l_Lean_Syntax_getOptional_x3f(v___x_4278_);
lean_dec(v___x_4278_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_box(0);
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4276_;
v___y_4232_ = v___y_4269_;
v___y_4233_ = v___y_4275_;
v___y_4234_ = v___y_4267_;
v___y_4235_ = v___y_4274_;
v___y_4236_ = v___y_4263_;
v___y_4237_ = v___y_4272_;
v___y_4238_ = v___y_4271_;
v___y_4239_ = v___y_4265_;
v___y_4240_ = v___y_4270_;
v___y_4241_ = v___y_4273_;
v___y_4242_ = v_args_4268_;
v___y_4243_ = v___x_4280_;
goto v___jp_4229_;
}
else
{
lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_val_4281_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4279_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_dec(v___x_4279_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_val_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4276_;
v___y_4232_ = v___y_4269_;
v___y_4233_ = v___y_4275_;
v___y_4234_ = v___y_4267_;
v___y_4235_ = v___y_4274_;
v___y_4236_ = v___y_4263_;
v___y_4237_ = v___y_4272_;
v___y_4238_ = v___y_4271_;
v___y_4239_ = v___y_4265_;
v___y_4240_ = v___y_4270_;
v___y_4241_ = v___y_4273_;
v___y_4242_ = v_args_4268_;
v___y_4243_ = v___x_4286_;
goto v___jp_4229_;
}
}
}
}
v___jp_4290_:
{
lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4305_ = l_Lean_Syntax_getArg(v___y_4294_, v___y_4292_);
v___x_4306_ = l_Lean_Syntax_isNone(v___x_4305_);
if (v___x_4306_ == 0)
{
uint8_t v___x_4307_; 
lean_inc(v___x_4305_);
v___x_4307_ = l_Lean_Syntax_matchesNull(v___x_4305_, v___x_4289_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec(v___x_4305_);
lean_dec(v_o_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4308_;
}
else
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4309_ = l_Lean_Syntax_getArg(v___x_4305_, v___x_3907_);
lean_dec(v___x_4305_);
v___x_4310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
lean_inc_ref(v___x_3894_);
v___x_4311_ = l_Lean_Name_mkStr4(v___x_3894_, v___x_3895_, v___x_3896_, v___x_4310_);
lean_inc(v___x_4309_);
v___x_4312_ = l_Lean_Syntax_isOfKind(v___x_4309_, v___x_4311_);
lean_dec(v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_dec(v___x_4309_);
lean_dec(v_o_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4313_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4313_;
}
else
{
lean_object* v___x_4314_; lean_object* v_args_4315_; lean_object* v___x_4316_; 
v___x_4314_ = l_Lean_Syntax_getArg(v___x_4309_, v___x_4289_);
lean_dec(v___x_4309_);
v_args_4315_ = l_Lean_Syntax_getArgs(v___x_4314_);
lean_dec(v___x_4314_);
v___x_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4316_, 0, v_args_4315_);
v___y_4263_ = v___y_4291_;
v___y_4264_ = v_o_4296_;
v___y_4265_ = v___y_4293_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v_args_4268_ = v___x_4316_;
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4298_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4300_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4303_;
v___y_4276_ = v___y_4304_;
goto v___jp_4262_;
}
}
}
else
{
lean_object* v___x_4317_; 
lean_dec(v___x_4305_);
v___x_4317_ = lean_box(0);
v___y_4263_ = v___y_4291_;
v___y_4264_ = v_o_4296_;
v___y_4265_ = v___y_4293_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v_args_4268_ = v___x_4317_;
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4298_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4300_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4303_;
v___y_4276_ = v___y_4304_;
goto v___jp_4262_;
}
}
v___jp_4318_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4328_ = lean_unsigned_to_nat(2u);
v___x_4329_ = l_Lean_Syntax_getArg(v_stx_3892_, v___x_4328_);
v___x_4330_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
lean_inc_ref(v___x_3894_);
v___x_4331_ = l_Lean_Name_mkStr4(v___x_3894_, v___x_3895_, v___x_3896_, v___x_4330_);
lean_inc(v___x_4329_);
v___x_4332_ = l_Lean_Syntax_isOfKind(v___x_4329_, v___x_4331_);
lean_dec(v___x_4331_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4333_; 
lean_dec(v___x_4329_);
lean_dec(v_bang_4319_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4333_;
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4334_ = l_Lean_Syntax_getArg(v___x_4329_, v___x_3907_);
v___x_4335_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
lean_inc_ref(v___x_3894_);
v___x_4336_ = l_Lean_Name_mkStr4(v___x_3894_, v___x_3895_, v___x_3896_, v___x_4335_);
lean_inc(v___x_4334_);
v___x_4337_ = l_Lean_Syntax_isOfKind(v___x_4334_, v___x_4336_);
lean_dec(v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec(v___x_4334_);
lean_dec(v___x_4329_);
lean_dec(v_bang_4319_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = l_Lean_Syntax_getArg(v___x_4329_, v___x_4289_);
v___x_4340_ = l_Lean_Syntax_isNone(v___x_4339_);
if (v___x_4340_ == 0)
{
uint8_t v___x_4341_; 
lean_inc(v___x_4339_);
v___x_4341_ = l_Lean_Syntax_matchesNull(v___x_4339_, v___x_4289_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; 
lean_dec(v___x_4339_);
lean_dec(v___x_4334_);
lean_dec(v___x_4329_);
lean_dec(v_bang_4319_);
lean_dec(v_tk_3908_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
lean_dec_ref(v___x_3894_);
v___x_4342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4342_;
}
else
{
lean_object* v_o_4343_; lean_object* v___x_4344_; 
v_o_4343_ = l_Lean_Syntax_getArg(v___x_4339_, v___x_3907_);
lean_dec(v___x_4339_);
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_o_4343_);
v___y_4291_ = v___x_4332_;
v___y_4292_ = v___x_4328_;
v___y_4293_ = v___x_4334_;
v___y_4294_ = v___x_4329_;
v___y_4295_ = v_bang_4319_;
v_o_4296_ = v___x_4344_;
v___y_4297_ = v___y_4320_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___y_4322_;
v___y_4300_ = v___y_4323_;
v___y_4301_ = v___y_4324_;
v___y_4302_ = v___y_4325_;
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___y_4327_;
goto v___jp_4290_;
}
}
else
{
lean_object* v___x_4345_; 
lean_dec(v___x_4339_);
v___x_4345_ = lean_box(0);
v___y_4291_ = v___x_4332_;
v___y_4292_ = v___x_4328_;
v___y_4293_ = v___x_4334_;
v___y_4294_ = v___x_4329_;
v___y_4295_ = v_bang_4319_;
v_o_4296_ = v___x_4345_;
v___y_4297_ = v___y_4320_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___y_4322_;
v___y_4300_ = v___y_4323_;
v___y_4301_ = v___y_4324_;
v___y_4302_ = v___y_4325_;
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___y_4327_;
goto v___jp_4290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4353_, lean_object* v_stx_4354_, lean_object* v___x_4355_, lean_object* v___x_4356_, lean_object* v___x_4357_, lean_object* v___x_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
uint8_t v___x_8014__boxed_4368_; uint8_t v___x_8015__boxed_4369_; lean_object* v_res_4370_; 
v___x_8014__boxed_4368_ = lean_unbox(v___x_4353_);
v___x_8015__boxed_4369_ = lean_unbox(v___x_4355_);
v_res_4370_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8014__boxed_4368_, v_stx_4354_, v___x_8015__boxed_4369_, v___x_4356_, v___x_4357_, v___x_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v_stx_4354_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___y_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4390_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4377_);
v___x_4391_ = l_Lean_Syntax_isOfKind(v_stx_4377_, v___x_4390_);
v___x_4392_ = 1;
v___x_4393_ = lean_box(v___x_4391_);
v___x_4394_ = lean_box(v___x_4392_);
v___y_4395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4395_, 0, v___x_4393_);
lean_closure_set(v___y_4395_, 1, v_stx_4377_);
lean_closure_set(v___y_4395_, 2, v___x_4394_);
lean_closure_set(v___y_4395_, 3, v___x_4387_);
lean_closure_set(v___y_4395_, 4, v___x_4388_);
lean_closure_set(v___y_4395_, 5, v___x_4389_);
v___x_4396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4396_, 0, v___y_4395_);
v___x_4397_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4396_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4416_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4417_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4416_, v___x_4417_, v___x_4418_, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4451_ = l_Lean_addBuiltinDeclarationRanges(v___x_4449_, v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4453_;
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
