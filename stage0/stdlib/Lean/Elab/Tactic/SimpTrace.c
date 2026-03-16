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
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 84, 117, 30, 74, 67, 74, 164)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSimpAllTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 119, 44, 227, 45, 220, 224)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalDSimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 218, 74, 127, 38, 51, 185, 136)}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object*);
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
lean_dec_ref(v___x_25_);
v_str_31_ = lean_ctor_get(v_pre_26_, 1);
lean_inc_ref(v_str_31_);
lean_dec_ref(v_pre_26_);
v_str_32_ = lean_ctor_get(v_pre_27_, 1);
lean_inc_ref(v_str_32_);
lean_dec_ref(v_pre_27_);
v_str_33_ = lean_ctor_get(v_pre_28_, 1);
lean_inc_ref(v_str_33_);
lean_dec_ref(v_pre_28_);
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
lean_dec_ref(v___x_48_);
v_str_54_ = lean_ctor_get(v_pre_49_, 1);
lean_inc_ref(v_str_54_);
lean_dec_ref(v_pre_49_);
v_str_55_ = lean_ctor_get(v_pre_50_, 1);
lean_inc_ref(v_str_55_);
lean_dec_ref(v_pre_50_);
v_str_56_ = lean_ctor_get(v_pre_51_, 1);
lean_inc_ref(v_str_56_);
lean_dec_ref(v_pre_51_);
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
v_id_67_ = lean_erase_macro_scopes(v___x_66_);
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
lean_dec_ref(v_pre_51_);
lean_dec_ref(v_pre_50_);
lean_dec_ref(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v_pre_50_);
lean_dec_ref(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec(v_pre_50_);
lean_dec_ref(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v_pre_28_);
lean_dec_ref(v_pre_27_);
lean_dec_ref(v_pre_26_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v_pre_27_);
lean_dec(v_pre_28_);
lean_dec_ref(v_pre_26_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v_pre_26_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v___x_25_);
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
uint8_t v___x_38834__boxed_208_; lean_object* v_res_209_; 
v___x_38834__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38834__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_38861__boxed_246_; lean_object* v_res_247_; 
v___x_38861__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_38861__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
lean_inc(v_head_264_);
v_tail_265_ = lean_ctor_get(v_as_x27_259_, 1);
lean_inc(v_tail_265_);
lean_dec_ref(v_as_x27_259_);
v_ref_266_ = lean_ctor_get(v___y_261_, 5);
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
lean_dec(v___x_278_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(lean_object* v_opts_284_, lean_object* v_opt_285_){
_start:
{
lean_object* v_name_286_; lean_object* v_defValue_287_; lean_object* v_map_288_; lean_object* v___x_289_; 
v_name_286_ = lean_ctor_get(v_opt_285_, 0);
v_defValue_287_ = lean_ctor_get(v_opt_285_, 1);
v_map_288_ = lean_ctor_get(v_opts_284_, 0);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_288_, v_name_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
uint8_t v___x_290_; 
v___x_290_ = lean_unbox(v_defValue_287_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref(v___x_289_);
if (lean_obj_tag(v_val_291_) == 1)
{
uint8_t v_v_292_; 
v_v_292_ = lean_ctor_get_uint8(v_val_291_, 0);
lean_dec_ref(v_val_291_);
return v_v_292_;
}
else
{
uint8_t v___x_293_; 
lean_dec(v_val_291_);
v___x_293_ = lean_unbox(v_defValue_287_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11___boxed(lean_object* v_opts_294_, lean_object* v_opt_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_opts_294_, v_opt_295_);
lean_dec_ref(v_opt_295_);
lean_dec_ref(v_opts_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_opt_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_options_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_options_301_ = lean_ctor_get(v___y_299_, 2);
v___x_302_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_options_301_, v_opt_298_);
v___x_303_ = lean_box(v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_opt_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v_opt_305_, v___y_306_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_opt_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_315_ = lean_st_ref_get(v___y_313_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_env_316_);
lean_dec(v___x_315_);
v___x_317_ = lean_st_ref_get(v___y_311_);
v_mctx_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_317_);
v_lctx_319_ = lean_ctor_get(v___y_310_, 2);
v_options_320_ = lean_ctor_get(v___y_312_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_316_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_309_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(uint8_t v___y_338_, uint8_t v_suppressElabErrors_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 1)
{
lean_object* v_pre_341_; 
v_pre_341_ = lean_ctor_get(v_x_340_, 0);
switch(lean_obj_tag(v_pre_341_))
{
case 1:
{
lean_object* v_pre_342_; 
v_pre_342_ = lean_ctor_get(v_pre_341_, 0);
switch(lean_obj_tag(v_pre_342_))
{
case 0:
{
lean_object* v_str_343_; lean_object* v_str_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_str_343_ = lean_ctor_get(v_x_340_, 1);
v_str_344_ = lean_ctor_get(v_pre_341_, 1);
v___x_345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0));
v___x_346_ = lean_string_dec_eq(v_str_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_348_ = lean_string_dec_eq(v_str_344_, v___x_347_);
if (v___x_348_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1));
v___x_350_ = lean_string_dec_eq(v_str_343_, v___x_349_);
if (v___x_350_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2));
v___x_352_ = lean_string_dec_eq(v_str_343_, v___x_351_);
if (v___x_352_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
case 1:
{
lean_object* v_pre_353_; 
v_pre_353_ = lean_ctor_get(v_pre_342_, 0);
if (lean_obj_tag(v_pre_353_) == 0)
{
lean_object* v_str_354_; lean_object* v_str_355_; lean_object* v_str_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_str_354_ = lean_ctor_get(v_x_340_, 1);
v_str_355_ = lean_ctor_get(v_pre_341_, 1);
v_str_356_ = lean_ctor_get(v_pre_342_, 1);
v___x_357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3));
v___x_358_ = lean_string_dec_eq(v_str_356_, v___x_357_);
if (v___x_358_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4));
v___x_360_ = lean_string_dec_eq(v_str_355_, v___x_359_);
if (v___x_360_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5));
v___x_362_ = lean_string_dec_eq(v_str_354_, v___x_361_);
if (v___x_362_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
}
else
{
return v___y_338_;
}
}
default: 
{
return v___y_338_;
}
}
}
case 0:
{
lean_object* v_str_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_str_363_ = lean_ctor_get(v_x_340_, 1);
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6));
v___x_365_ = lean_string_dec_eq(v_str_363_, v___x_364_);
if (v___x_365_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
default: 
{
return v___y_338_;
}
}
}
else
{
return v___y_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed(lean_object* v___y_366_, lean_object* v_suppressElabErrors_367_, lean_object* v_x_368_){
_start:
{
uint8_t v___y_39045__boxed_369_; uint8_t v_suppressElabErrors_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v___y_39045__boxed_369_ = lean_unbox(v___y_366_);
v_suppressElabErrors_boxed_370_ = lean_unbox(v_suppressElabErrors_367_);
v_res_371_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(v___y_39045__boxed_369_, v_suppressElabErrors_boxed_370_, v_x_368_);
lean_dec(v_x_368_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(lean_object* v_ref_374_, lean_object* v_msgData_375_, uint8_t v_severity_376_, uint8_t v_isSilent_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_420_; uint8_t v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v___y_425_; uint8_t v___y_426_; lean_object* v___y_427_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; uint8_t v___x_467_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; uint8_t v___y_474_; uint8_t v___y_475_; uint8_t v___y_477_; uint8_t v___x_492_; 
v___x_467_ = 2;
v___x_492_ = l_Lean_instBEqMessageSeverity_beq(v_severity_376_, v___x_467_);
if (v___x_492_ == 0)
{
v___y_477_ = v___x_492_;
goto v___jp_476_;
}
else
{
uint8_t v___x_493_; 
lean_inc_ref(v_msgData_375_);
v___x_493_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_375_);
v___y_477_ = v___x_493_;
goto v___jp_476_;
}
v___jp_383_:
{
lean_object* v___x_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_env_396_; lean_object* v_nextMacroScope_397_; lean_object* v_ngen_398_; lean_object* v_auxDeclNGen_399_; lean_object* v_traceState_400_; lean_object* v_cache_401_; lean_object* v_messages_402_; lean_object* v_infoState_403_; lean_object* v_snapshotTasks_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_418_; 
v___x_393_ = lean_st_ref_take(v___y_392_);
v_currNamespace_394_ = lean_ctor_get(v___y_391_, 6);
lean_inc(v_currNamespace_394_);
v_openDecls_395_ = lean_ctor_get(v___y_391_, 7);
lean_inc(v_openDecls_395_);
lean_dec_ref(v___y_391_);
v_env_396_ = lean_ctor_get(v___x_393_, 0);
v_nextMacroScope_397_ = lean_ctor_get(v___x_393_, 1);
v_ngen_398_ = lean_ctor_get(v___x_393_, 2);
v_auxDeclNGen_399_ = lean_ctor_get(v___x_393_, 3);
v_traceState_400_ = lean_ctor_get(v___x_393_, 4);
v_cache_401_ = lean_ctor_get(v___x_393_, 5);
v_messages_402_ = lean_ctor_get(v___x_393_, 6);
v_infoState_403_ = lean_ctor_get(v___x_393_, 7);
v_snapshotTasks_404_ = lean_ctor_get(v___x_393_, 8);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_418_ == 0)
{
v___x_406_ = v___x_393_;
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snapshotTasks_404_);
lean_inc(v_infoState_403_);
lean_inc(v_messages_402_);
lean_inc(v_cache_401_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_399_);
lean_inc(v_ngen_398_);
lean_inc(v_nextMacroScope_397_);
lean_inc(v_env_396_);
lean_dec(v___x_393_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_currNamespace_394_);
lean_ctor_set(v___x_408_, 1, v_openDecls_395_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___y_390_);
v___x_410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_410_, 0, v___y_388_);
lean_ctor_set(v___x_410_, 1, v___y_389_);
lean_ctor_set(v___x_410_, 2, v___y_385_);
lean_ctor_set(v___x_410_, 3, v___y_386_);
lean_ctor_set(v___x_410_, 4, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5, v___y_387_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 1, v___y_384_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 2, v_isSilent_377_);
v___x_411_ = l_Lean_MessageLog_add(v___x_410_, v_messages_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 6, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_env_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_nextMacroScope_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_ngen_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_auxDeclNGen_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_traceState_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_cache_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_infoState_403_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_snapshotTasks_404_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_st_ref_set(v___y_392_, v___x_413_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
v___jp_419_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_443_; 
v___x_428_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_375_);
v___x_429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v___x_428_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_443_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc_ref(v___y_423_);
v___x_434_ = l_Lean_FileMap_toPosition(v___y_423_, v___y_422_);
lean_dec(v___y_422_);
v___x_435_ = l_Lean_FileMap_toPosition(v___y_423_, v___y_427_);
lean_dec(v___y_427_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0));
if (v___y_426_ == 0)
{
lean_del_object(v___x_432_);
lean_dec_ref(v___y_420_);
v___y_384_ = v___y_421_;
v___y_385_ = v___x_436_;
v___y_386_ = v___x_437_;
v___y_387_ = v___y_424_;
v___y_388_ = v___y_425_;
v___y_389_ = v___x_434_;
v___y_390_ = v_a_430_;
v___y_391_ = v___y_380_;
v___y_392_ = v___y_381_;
goto v___jp_383_;
}
else
{
uint8_t v___x_438_; 
lean_inc(v_a_430_);
v___x_438_ = l_Lean_MessageData_hasTag(v___y_420_, v_a_430_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_dec_ref(v___x_436_);
lean_dec_ref(v___x_434_);
lean_dec(v_a_430_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v___y_380_);
v___x_439_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_439_);
v___x_441_ = v___x_432_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_del_object(v___x_432_);
v___y_384_ = v___y_421_;
v___y_385_ = v___x_436_;
v___y_386_ = v___x_437_;
v___y_387_ = v___y_424_;
v___y_388_ = v___y_425_;
v___y_389_ = v___x_434_;
v___y_390_ = v_a_430_;
v___y_391_ = v___y_380_;
v___y_392_ = v___y_381_;
goto v___jp_383_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Syntax_getTailPos_x3f(v___y_451_, v___y_448_);
lean_dec(v___y_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_inc(v___y_452_);
v___y_420_ = v___y_445_;
v___y_421_ = v___y_446_;
v___y_422_ = v___y_452_;
v___y_423_ = v___y_447_;
v___y_424_ = v___y_448_;
v___y_425_ = v___y_449_;
v___y_426_ = v___y_450_;
v___y_427_ = v___y_452_;
goto v___jp_419_;
}
else
{
lean_object* v_val_454_; 
v_val_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_454_);
lean_dec_ref(v___x_453_);
v___y_420_ = v___y_445_;
v___y_421_ = v___y_446_;
v___y_422_ = v___y_452_;
v___y_423_ = v___y_447_;
v___y_424_ = v___y_448_;
v___y_425_ = v___y_449_;
v___y_426_ = v___y_450_;
v___y_427_ = v_val_454_;
goto v___jp_419_;
}
}
v___jp_455_:
{
lean_object* v_ref_463_; lean_object* v___x_464_; 
v_ref_463_ = l_Lean_replaceRef(v_ref_374_, v___y_461_);
lean_dec(v___y_461_);
v___x_464_ = l_Lean_Syntax_getPos_x3f(v_ref_463_, v___y_458_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_462_;
v___y_447_ = v___y_457_;
v___y_448_ = v___y_458_;
v___y_449_ = v___y_459_;
v___y_450_ = v___y_460_;
v___y_451_ = v_ref_463_;
v___y_452_ = v___x_465_;
goto v___jp_444_;
}
else
{
lean_object* v_val_466_; 
v_val_466_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_466_);
lean_dec_ref(v___x_464_);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_462_;
v___y_447_ = v___y_457_;
v___y_448_ = v___y_458_;
v___y_449_ = v___y_459_;
v___y_450_ = v___y_460_;
v___y_451_ = v_ref_463_;
v___y_452_ = v_val_466_;
goto v___jp_444_;
}
}
v___jp_468_:
{
if (v___y_475_ == 0)
{
v___y_456_ = v___y_470_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_474_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_473_;
v___y_461_ = v___y_472_;
v___y_462_ = v_severity_376_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___y_470_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_474_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_473_;
v___y_461_ = v___y_472_;
v___y_462_ = v___x_467_;
goto v___jp_455_;
}
}
v___jp_476_:
{
if (v___y_477_ == 0)
{
lean_object* v_fileName_478_; lean_object* v_fileMap_479_; lean_object* v_options_480_; lean_object* v_ref_481_; uint8_t v_suppressElabErrors_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___f_485_; uint8_t v___x_486_; uint8_t v___x_487_; 
v_fileName_478_ = lean_ctor_get(v___y_380_, 0);
v_fileMap_479_ = lean_ctor_get(v___y_380_, 1);
v_options_480_ = lean_ctor_get(v___y_380_, 2);
v_ref_481_ = lean_ctor_get(v___y_380_, 5);
v_suppressElabErrors_482_ = lean_ctor_get_uint8(v___y_380_, sizeof(void*)*14 + 1);
v___x_483_ = lean_box(v___y_477_);
v___x_484_ = lean_box(v_suppressElabErrors_482_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_485_, 0, v___x_483_);
lean_closure_set(v___f_485_, 1, v___x_484_);
v___x_486_ = 1;
v___x_487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_376_, v___x_486_);
if (v___x_487_ == 0)
{
lean_inc(v_ref_481_);
lean_inc_ref(v_fileName_478_);
lean_inc_ref(v_fileMap_479_);
v___y_469_ = v_fileMap_479_;
v___y_470_ = v___f_485_;
v___y_471_ = v_fileName_478_;
v___y_472_ = v_ref_481_;
v___y_473_ = v_suppressElabErrors_482_;
v___y_474_ = v___y_477_;
v___y_475_ = v___x_487_;
goto v___jp_468_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = l_Lean_warningAsError;
v___x_489_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_options_480_, v___x_488_);
lean_inc(v_ref_481_);
lean_inc_ref(v_fileName_478_);
lean_inc_ref(v_fileMap_479_);
v___y_469_ = v_fileMap_479_;
v___y_470_ = v___f_485_;
v___y_471_ = v_fileName_478_;
v___y_472_ = v_ref_481_;
v___y_473_ = v_suppressElabErrors_482_;
v___y_474_ = v___y_477_;
v___y_475_ = v___x_489_;
goto v___jp_468_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v___y_380_);
lean_dec_ref(v_msgData_375_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___boxed(lean_object* v_ref_494_, lean_object* v_msgData_495_, lean_object* v_severity_496_, lean_object* v_isSilent_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v_severity_boxed_503_; uint8_t v_isSilent_boxed_504_; lean_object* v_res_505_; 
v_severity_boxed_503_ = lean_unbox(v_severity_496_);
v_isSilent_boxed_504_ = lean_unbox(v_isSilent_497_);
v_res_505_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_494_, v_msgData_495_, v_severity_boxed_503_, v_isSilent_boxed_504_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_ref_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(lean_object* v_msgData_506_, uint8_t v_severity_507_, uint8_t v_isSilent_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_ref_518_; lean_object* v___x_519_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 5);
lean_inc(v_ref_518_);
v___x_519_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_518_, v_msgData_506_, v_severity_507_, v_isSilent_508_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v_ref_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13___boxed(lean_object* v_msgData_520_, lean_object* v_severity_521_, lean_object* v_isSilent_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_severity_boxed_532_; uint8_t v_isSilent_boxed_533_; lean_object* v_res_534_; 
v_severity_boxed_532_ = lean_unbox(v_severity_521_);
v_isSilent_boxed_533_ = lean_unbox(v_isSilent_522_);
v_res_534_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(v_msgData_520_, v_severity_boxed_532_, v_isSilent_boxed_533_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 1;
v___x_546_ = 0;
v___x_547_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(v_msgData_535_, v___x_545_, v___x_546_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(v_msgData_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_id_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_env_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_598_; 
v___x_575_ = lean_st_ref_get(v___y_573_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_578_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v___x_577_, v___y_572_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_598_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v_isExporting_588_; 
v_isExporting_588_ = lean_ctor_get_uint8(v_env_576_, sizeof(void*)*8);
lean_dec_ref(v_env_576_);
if (v_isExporting_588_ == 0)
{
lean_dec(v_a_579_);
lean_dec_ref(v___y_572_);
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_isPrivateName(v_id_565_);
if (v___x_589_ == 0)
{
lean_dec(v_a_579_);
lean_dec_ref(v___y_572_);
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
if (v___x_590_ == 0)
{
lean_dec_ref(v___y_572_);
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_581_);
v___x_591_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1);
v___x_592_ = 0;
v___x_593_ = l_Lean_MessageData_ofConstName(v_id_565_, v___x_592_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(v___x_596_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_597_;
}
}
}
v___jp_583_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_box(0);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_id_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_id_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_609_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(lean_object* v_x_610_){
_start:
{
lean_object* v_fst_611_; uint8_t v___x_612_; 
v_fst_611_ = lean_ctor_get(v_x_610_, 0);
v___x_612_ = l_Lean_isPrivateName(v_fst_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(v_x_613_);
lean_dec_ref(v_x_613_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
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
v_options_630_ = lean_ctor_get(v___y_625_, 2);
v_currNamespace_631_ = lean_ctor_get(v___y_625_, 6);
v_openDecls_632_ = lean_ctor_get(v___y_625_, 7);
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
lean_dec_ref(v___y_625_);
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
lean_dec_ref(v___y_625_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_res_635_);
return v___x_638_;
}
else
{
lean_object* v___f_639_; lean_object* v___x_640_; 
v___f_639_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0));
lean_inc(v_res_635_);
v___x_640_ = l_List_find_x3f___redArg(v___f_639_, v_res_635_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v_fst_642_; lean_object* v___x_643_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref(v___x_640_);
v_fst_642_ = lean_ctor_get(v_val_641_, 0);
lean_inc(v_fst_642_);
lean_dec(v_val_641_);
v___x_643_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_fst_642_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_651_);
v___x_645_ = v___x_643_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_dec(v___x_643_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_res_635_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_res_635_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_res_635_);
v_a_652_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_643_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_643_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v___x_640_);
lean_dec_ref(v___y_625_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_res_635_);
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_661_, lean_object* v_enableLog_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v_enableLog_boxed_672_; lean_object* v_res_673_; 
v_enableLog_boxed_672_ = lean_unbox(v_enableLog_662_);
v_res_673_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_661_, v_enableLog_boxed_672_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_List_reverse___redArg(v_a_675_);
return v___x_676_;
}
else
{
lean_object* v_head_677_; lean_object* v_tail_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_head_677_ = lean_ctor_get(v_a_674_, 0);
v_tail_678_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v_a_674_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_tail_678_);
lean_inc(v_head_677_);
lean_dec(v_a_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v___x_684_; 
v_fst_682_ = lean_ctor_get(v_head_677_, 0);
lean_inc(v_fst_682_);
lean_dec(v_head_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_a_675_);
lean_ctor_set(v___x_680_, 0, v_fst_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_675_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_a_674_ = v_tail_678_;
v_a_675_ = v___x_684_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_ref_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_ref_694_ = lean_ctor_get(v___y_691_, 5);
v___x_695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_ref_694_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_ref_694_);
lean_ctor_set(v___x_700_, 1, v_a_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_fileName_723_; lean_object* v_fileMap_724_; lean_object* v_options_725_; lean_object* v_currRecDepth_726_; lean_object* v_maxRecDepth_727_; lean_object* v_ref_728_; lean_object* v_currNamespace_729_; lean_object* v_openDecls_730_; lean_object* v_initHeartbeats_731_; lean_object* v_maxHeartbeats_732_; lean_object* v_quotContext_733_; lean_object* v_currMacroScope_734_; uint8_t v_diag_735_; lean_object* v_cancelTk_x3f_736_; uint8_t v_suppressElabErrors_737_; lean_object* v_inheritedTraceOptions_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_747_; 
v_fileName_723_ = lean_ctor_get(v___y_720_, 0);
v_fileMap_724_ = lean_ctor_get(v___y_720_, 1);
v_options_725_ = lean_ctor_get(v___y_720_, 2);
v_currRecDepth_726_ = lean_ctor_get(v___y_720_, 3);
v_maxRecDepth_727_ = lean_ctor_get(v___y_720_, 4);
v_ref_728_ = lean_ctor_get(v___y_720_, 5);
v_currNamespace_729_ = lean_ctor_get(v___y_720_, 6);
v_openDecls_730_ = lean_ctor_get(v___y_720_, 7);
v_initHeartbeats_731_ = lean_ctor_get(v___y_720_, 8);
v_maxHeartbeats_732_ = lean_ctor_get(v___y_720_, 9);
v_quotContext_733_ = lean_ctor_get(v___y_720_, 10);
v_currMacroScope_734_ = lean_ctor_get(v___y_720_, 11);
v_diag_735_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*14);
v_cancelTk_x3f_736_ = lean_ctor_get(v___y_720_, 12);
v_suppressElabErrors_737_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_738_ = lean_ctor_get(v___y_720_, 13);
v_isSharedCheck_747_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_747_ == 0)
{
v___x_740_ = v___y_720_;
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_inheritedTraceOptions_738_);
lean_inc(v_cancelTk_x3f_736_);
lean_inc(v_currMacroScope_734_);
lean_inc(v_quotContext_733_);
lean_inc(v_maxHeartbeats_732_);
lean_inc(v_initHeartbeats_731_);
lean_inc(v_openDecls_730_);
lean_inc(v_currNamespace_729_);
lean_inc(v_ref_728_);
lean_inc(v_maxRecDepth_727_);
lean_inc(v_currRecDepth_726_);
lean_inc(v_options_725_);
lean_inc(v_fileMap_724_);
lean_inc(v_fileName_723_);
lean_dec(v___y_720_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_ref_742_; lean_object* v___x_744_; 
v_ref_742_ = l_Lean_replaceRef(v_ref_712_, v_ref_728_);
lean_dec(v_ref_728_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 5, v_ref_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_fileName_723_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_fileMap_724_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_options_725_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_currRecDepth_726_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_maxRecDepth_727_);
lean_ctor_set(v_reuseFailAlloc_746_, 5, v_ref_742_);
lean_ctor_set(v_reuseFailAlloc_746_, 6, v_currNamespace_729_);
lean_ctor_set(v_reuseFailAlloc_746_, 7, v_openDecls_730_);
lean_ctor_set(v_reuseFailAlloc_746_, 8, v_initHeartbeats_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 9, v_maxHeartbeats_732_);
lean_ctor_set(v_reuseFailAlloc_746_, 10, v_quotContext_733_);
lean_ctor_set(v_reuseFailAlloc_746_, 11, v_currMacroScope_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 12, v_cancelTk_x3f_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 13, v_inheritedTraceOptions_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, sizeof(void*)*14, v_diag_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, sizeof(void*)*14 + 1, v_suppressElabErrors_737_);
v___x_744_ = v_reuseFailAlloc_746_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_713_, v___y_718_, v___y_719_, v___x_744_, v___y_721_);
lean_dec_ref(v___x_744_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_748_, lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_748_, v_msg_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v_ref_748_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v___x_763_);
lean_ctor_set(v___x_765_, 4, v___x_763_);
lean_ctor_set(v___x_765_, 5, v___x_763_);
lean_ctor_set(v___x_765_, 6, v___x_763_);
lean_ctor_set(v___x_765_, 7, v___x_763_);
lean_ctor_set(v___x_765_, 8, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3(void){
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3);
v___x_774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_770_);
lean_ctor_set_usize(v___x_774_, 4, v___x_769_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(1);
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(lean_object* v_msg_800_, lean_object* v_declHint_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_env_805_; uint8_t v___x_806_; 
v___x_804_ = lean_st_ref_get(v___y_802_);
v_env_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_804_);
v___x_806_ = l_Lean_Name_isAnonymous(v_declHint_801_);
if (v___x_806_ == 0)
{
uint8_t v_isExporting_807_; 
v_isExporting_807_ = lean_ctor_get_uint8(v_env_805_, sizeof(void*)*8);
if (v_isExporting_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_msg_800_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
lean_inc_ref(v_env_805_);
v___x_809_ = l_Lean_Environment_setExporting(v_env_805_, v___x_806_);
lean_inc(v_declHint_801_);
lean_inc_ref(v___x_809_);
v___x_810_ = l_Lean_Environment_contains(v___x_809_, v_declHint_801_, v_isExporting_807_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v___x_809_);
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_msg_800_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_c_817_; lean_object* v___x_818_; 
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5);
v___x_814_ = l_Lean_Options_empty;
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v___x_809_);
lean_ctor_set(v___x_815_, 1, v___x_812_);
lean_ctor_set(v___x_815_, 2, v___x_813_);
lean_ctor_set(v___x_815_, 3, v___x_814_);
lean_inc(v_declHint_801_);
v___x_816_ = l_Lean_MessageData_ofConstName(v_declHint_801_, v___x_806_);
v_c_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_817_, 0, v___x_815_);
lean_ctor_set(v_c_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_805_, v_declHint_801_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_c_817_);
v___x_821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_MessageData_note(v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v_msg_800_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_861_; 
v_val_826_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_861_ == 0)
{
v___x_828_ = v___x_818_;
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v___x_818_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_mod_833_; uint8_t v___x_834_; 
v___x_830_ = lean_box(0);
v___x_831_ = l_Lean_Environment_header(v_env_805_);
lean_dec_ref(v_env_805_);
v___x_832_ = l_Lean_EnvironmentHeader_moduleNames(v___x_831_);
v_mod_833_ = lean_array_get(v___x_830_, v___x_832_, v_val_826_);
lean_dec(v_val_826_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_isPrivateName(v_declHint_801_);
lean_dec(v_declHint_801_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_c_817_);
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_MessageData_note(v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v_msg_800_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_844_);
v___x_846_ = v___x_828_;
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
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_c_817_);
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_800_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_857_);
v___x_859_ = v___x_828_;
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
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_msg_800_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___boxed(lean_object* v_msg_863_, lean_object* v_declHint_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_863_, v_declHint_864_, v___y_865_);
lean_dec(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(lean_object* v_msg_868_, lean_object* v_declHint_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v___x_879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_868_, v_declHint_869_, v___y_877_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18___boxed(lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(v_msg_890_, v_declHint_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_ref_902_, lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_916_; 
v___x_914_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(v_msg_903_, v_declHint_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_902_, v_a_915_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_ref_917_, lean_object* v_msg_918_, lean_object* v_declHint_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_917_, v_msg_918_, v_declHint_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
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
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(lean_object* v_ref_936_, lean_object* v_constName_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_947_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1);
v___x_948_ = 0;
lean_inc(v_constName_937_);
v___x_949_ = l_Lean_MessageData_ofConstName(v_constName_937_, v___x_948_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_947_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_936_, v___x_952_, v_constName_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_ref_954_, lean_object* v_constName_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_954_, v_constName_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
if (lean_obj_tag(v_a_966_) == 0)
{
lean_object* v___x_968_; 
v___x_968_ = l_List_reverse___redArg(v_a_967_);
return v___x_968_;
}
else
{
lean_object* v_head_969_; lean_object* v_tail_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_981_; 
v_head_969_ = lean_ctor_get(v_a_966_, 0);
v_tail_970_ = lean_ctor_get(v_a_966_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_981_ == 0)
{
v___x_972_ = v_a_966_;
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_tail_970_);
lean_inc(v_head_969_);
lean_dec(v_a_966_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_snd_974_; uint8_t v___x_975_; 
v_snd_974_ = lean_ctor_get(v_head_969_, 1);
v___x_975_ = l_List_isEmpty___redArg(v_snd_974_);
if (v___x_975_ == 0)
{
lean_del_object(v___x_972_);
lean_dec(v_head_969_);
v_a_966_ = v_tail_970_;
goto _start;
}
else
{
lean_object* v___x_978_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v_a_967_);
v___x_978_ = v___x_972_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_head_969_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_a_967_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
v_a_966_ = v_tail_970_;
v_a_967_ = v___x_978_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_982_, lean_object* v_cs_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v_cs_994_; uint8_t v___x_998_; 
v___x_993_ = lean_box(0);
v_cs_994_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(v_cs_983_, v___x_993_);
v___x_998_ = l_List_isEmpty___redArg(v_cs_994_);
if (v___x_998_ == 0)
{
lean_dec_ref(v___y_990_);
lean_dec(v_n_982_);
goto v___jp_995_;
}
else
{
lean_object* v_ref_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_cs_994_);
v_ref_999_ = lean_ctor_get(v___y_990_, 5);
lean_inc(v_ref_999_);
v___x_1000_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_999_, v_n_982_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v_ref_999_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_994_, v___x_993_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1009_, lean_object* v_cs_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1009_, v_cs_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 1;
lean_inc_ref(v___y_1028_);
lean_inc(v_n_1021_);
v___x_1032_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1021_, v___x_1031_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1021_, v_a_1033_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1034_;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v___y_1028_);
lean_dec(v_n_1021_);
v_a_1035_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1032_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
if (lean_obj_tag(v_a_1054_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_array_to_list(v_a_1055_);
return v___x_1056_;
}
else
{
lean_object* v_head_1057_; 
v_head_1057_ = lean_ctor_get(v_a_1054_, 0);
if (lean_obj_tag(v_head_1057_) == 1)
{
lean_object* v_fields_1058_; 
v_fields_1058_ = lean_ctor_get(v_head_1057_, 1);
if (lean_obj_tag(v_fields_1058_) == 0)
{
lean_object* v_tail_1059_; lean_object* v_n_1060_; lean_object* v___x_1061_; 
lean_inc_ref(v_head_1057_);
v_tail_1059_ = lean_ctor_get(v_a_1054_, 1);
lean_inc(v_tail_1059_);
lean_dec_ref(v_a_1054_);
v_n_1060_ = lean_ctor_get(v_head_1057_, 0);
lean_inc(v_n_1060_);
lean_dec_ref(v_head_1057_);
v___x_1061_ = lean_array_push(v_a_1055_, v_n_1060_);
v_a_1054_ = v_tail_1059_;
v_a_1055_ = v___x_1061_;
goto _start;
}
else
{
lean_object* v_tail_1063_; 
v_tail_1063_ = lean_ctor_get(v_a_1054_, 1);
lean_inc(v_tail_1063_);
lean_dec_ref(v_a_1054_);
v_a_1054_ = v_tail_1063_;
goto _start;
}
}
else
{
lean_object* v_tail_1065_; 
v_tail_1065_ = lean_ctor_get(v_a_1054_, 1);
lean_inc(v_tail_1065_);
lean_dec_ref(v_a_1054_);
v_a_1054_ = v_tail_1065_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1073_ = l_Lean_MessageData_ofFormat(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1074_, lean_object* v_k_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
if (lean_obj_tag(v_stx_1074_) == 3)
{
lean_object* v_val_1085_; lean_object* v_preresolved_1086_; lean_object* v___x_1087_; lean_object* v_pre_1088_; uint8_t v___x_1089_; 
v_val_1085_ = lean_ctor_get(v_stx_1074_, 2);
lean_inc(v_val_1085_);
v_preresolved_1086_ = lean_ctor_get(v_stx_1074_, 3);
v___x_1087_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1086_);
v_pre_1088_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1086_, v___x_1087_);
v___x_1089_ = l_List_isEmpty___redArg(v_pre_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v_val_1085_);
lean_dec_ref(v_stx_1074_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_k_1075_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_pre_1088_);
return v___x_1090_;
}
else
{
lean_object* v_fileName_1091_; lean_object* v_fileMap_1092_; lean_object* v_options_1093_; lean_object* v_currRecDepth_1094_; lean_object* v_maxRecDepth_1095_; lean_object* v_ref_1096_; lean_object* v_currNamespace_1097_; lean_object* v_openDecls_1098_; lean_object* v_initHeartbeats_1099_; lean_object* v_maxHeartbeats_1100_; lean_object* v_quotContext_1101_; lean_object* v_currMacroScope_1102_; uint8_t v_diag_1103_; lean_object* v_cancelTk_x3f_1104_; uint8_t v_suppressElabErrors_1105_; lean_object* v_inheritedTraceOptions_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_pre_1088_);
v_fileName_1091_ = lean_ctor_get(v___y_1082_, 0);
v_fileMap_1092_ = lean_ctor_get(v___y_1082_, 1);
v_options_1093_ = lean_ctor_get(v___y_1082_, 2);
v_currRecDepth_1094_ = lean_ctor_get(v___y_1082_, 3);
v_maxRecDepth_1095_ = lean_ctor_get(v___y_1082_, 4);
v_ref_1096_ = lean_ctor_get(v___y_1082_, 5);
v_currNamespace_1097_ = lean_ctor_get(v___y_1082_, 6);
v_openDecls_1098_ = lean_ctor_get(v___y_1082_, 7);
v_initHeartbeats_1099_ = lean_ctor_get(v___y_1082_, 8);
v_maxHeartbeats_1100_ = lean_ctor_get(v___y_1082_, 9);
v_quotContext_1101_ = lean_ctor_get(v___y_1082_, 10);
v_currMacroScope_1102_ = lean_ctor_get(v___y_1082_, 11);
v_diag_1103_ = lean_ctor_get_uint8(v___y_1082_, sizeof(void*)*14);
v_cancelTk_x3f_1104_ = lean_ctor_get(v___y_1082_, 12);
v_suppressElabErrors_1105_ = lean_ctor_get_uint8(v___y_1082_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1106_ = lean_ctor_get(v___y_1082_, 13);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1082_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1108_ = v___y_1082_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_inheritedTraceOptions_1106_);
lean_inc(v_cancelTk_x3f_1104_);
lean_inc(v_currMacroScope_1102_);
lean_inc(v_quotContext_1101_);
lean_inc(v_maxHeartbeats_1100_);
lean_inc(v_initHeartbeats_1099_);
lean_inc(v_openDecls_1098_);
lean_inc(v_currNamespace_1097_);
lean_inc(v_ref_1096_);
lean_inc(v_maxRecDepth_1095_);
lean_inc(v_currRecDepth_1094_);
lean_inc(v_options_1093_);
lean_inc(v_fileMap_1092_);
lean_inc(v_fileName_1091_);
lean_dec(v___y_1082_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_ref_1110_; lean_object* v___x_1112_; 
v_ref_1110_ = l_Lean_replaceRef(v_stx_1074_, v_ref_1096_);
lean_dec(v_ref_1096_);
lean_dec_ref(v_stx_1074_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 5, v_ref_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_fileName_1091_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_fileMap_1092_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_options_1093_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_currRecDepth_1094_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_maxRecDepth_1095_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_ref_1110_);
lean_ctor_set(v_reuseFailAlloc_1114_, 6, v_currNamespace_1097_);
lean_ctor_set(v_reuseFailAlloc_1114_, 7, v_openDecls_1098_);
lean_ctor_set(v_reuseFailAlloc_1114_, 8, v_initHeartbeats_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 9, v_maxHeartbeats_1100_);
lean_ctor_set(v_reuseFailAlloc_1114_, 10, v_quotContext_1101_);
lean_ctor_set(v_reuseFailAlloc_1114_, 11, v_currMacroScope_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 12, v_cancelTk_x3f_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 13, v_inheritedTraceOptions_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*14, v_diag_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*14 + 1, v_suppressElabErrors_1105_);
v___x_1112_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_10(v_k_1075_, v_val_1085_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___x_1112_, v___y_1083_, lean_box(0));
return v___x_1113_;
}
}
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_k_1075_);
v___x_1116_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1117_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1074_, v___x_1116_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v_stx_1074_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1118_, lean_object* v_k_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1118_, v_k_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1142_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1131_, v___x_1141_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_b_1157_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v_name_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1169_ = lean_array_uget_borrowed(v_as_1154_, v_i_1156_);
v_name_1170_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_name_1170_);
v___x_1171_ = lean_mk_syntax_ident(v_name_1170_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___x_1171_);
v___x_1172_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1171_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1171_, v_a_1173_, v_b_1157_, v___y_1164_);
lean_dec(v___x_1171_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; size_t v___x_1176_; size_t v___x_1177_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = lean_usize_add(v_i_1156_, v___x_1176_);
v_i_1156_ = v___x_1177_;
v_b_1157_ = v_a_1175_;
goto _start;
}
else
{
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v___x_1171_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_b_1157_);
v_a_1179_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1172_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1172_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1187_, lean_object* v_sz_1188_, lean_object* v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
size_t v_sz_boxed_1200_; size_t v_i_boxed_1201_; lean_object* v_res_1202_; 
v_sz_boxed_1200_ = lean_unbox_usize(v_sz_1188_);
lean_dec(v_sz_1188_);
v_i_boxed_1201_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1187_, v_sz_boxed_1200_, v_i_boxed_1201_, v_b_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec_ref(v_as_1187_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1222_, lean_object* v_stx_1223_, uint8_t v___x_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v___f_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
if (v___x_1222_ == 0)
{
lean_object* v___x_1238_; 
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_1238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v_tk_1240_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; uint8_t v___y_1314_; lean_object* v___y_1315_; lean_object* v_stxForSuggestion_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; uint8_t v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_stxForExecution_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; uint8_t v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; uint8_t v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; uint8_t v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; uint8_t v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; uint8_t v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; uint8_t v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; uint8_t v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; uint8_t v___y_1829_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v_argsArray_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; uint8_t v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v_args_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___x_2036_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_o_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v_bang_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v_tk_1240_ = l_Lean_Syntax_getArg(v_stx_1223_, v___x_1239_);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2095_ = l_Lean_Syntax_getArg(v_stx_1223_, v___x_2036_);
v___x_2096_ = l_Lean_Syntax_isNone(v___x_2095_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; 
lean_inc(v___x_2095_);
v___x_2097_ = l_Lean_Syntax_matchesNull(v___x_2095_, v___x_2036_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v___x_2095_);
lean_dec(v_tk_1240_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2098_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2098_;
}
else
{
lean_object* v_bang_2099_; lean_object* v___x_2100_; 
v_bang_2099_ = l_Lean_Syntax_getArg(v___x_2095_, v___x_1239_);
lean_dec(v___x_2095_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_bang_2099_);
v_bang_2067_ = v___x_2100_;
v___y_2068_ = v___y_1229_;
v___y_2069_ = v___y_1230_;
v___y_2070_ = v___y_1231_;
v___y_2071_ = v___y_1232_;
v___y_2072_ = v___y_1233_;
v___y_2073_ = v___y_1234_;
v___y_2074_ = v___y_1235_;
v___y_2075_ = v___y_1236_;
goto v___jp_2066_;
}
}
else
{
lean_object* v___x_2101_; 
lean_dec(v___x_2095_);
v___x_2101_ = lean_box(0);
v_bang_2067_ = v___x_2101_;
v___y_2068_ = v___y_1229_;
v___y_2069_ = v___y_1230_;
v___y_2070_ = v___y_1231_;
v___y_2071_ = v___y_1232_;
v___y_2072_ = v___y_1233_;
v___y_2073_ = v___y_1234_;
v___y_2074_ = v___y_1235_;
v___y_2075_ = v___y_1236_;
goto v___jp_2066_;
}
v___jp_1241_:
{
lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(v___x_1224_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1256_, 0, v___y_1244_);
lean_closure_set(v___f_1256_, 1, v___x_1239_);
lean_closure_set(v___f_1256_, 2, v___x_1255_);
lean_closure_set(v___f_1256_, 3, v___y_1254_);
lean_closure_set(v___f_1256_, 4, v___y_1243_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1250_);
v___x_1257_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1242_, v___f_1256_, v___y_1252_, v___y_1246_, v___y_1248_, v___y_1247_, v___y_1250_, v___y_1253_, v___y_1249_, v___y_1245_);
lean_dec(v___y_1242_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_usedTheorems_1259_; lean_object* v_diag_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1301_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v_usedTheorems_1259_ = lean_ctor_get(v_a_1258_, 0);
v_diag_1260_ = lean_ctor_get(v_a_1258_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_a_1258_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1262_ = v_a_1258_;
v_isShared_1263_ = v_isSharedCheck_1301_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_diag_1260_);
lean_inc(v_usedTheorems_1259_);
lean_dec(v_a_1258_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1301_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; 
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1249_);
v___x_1264_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1251_, v_usedTheorems_1259_, v___y_1250_, v___y_1253_, v___y_1249_, v___y_1245_);
lean_dec_ref(v_usedTheorems_1259_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v_ref_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v_ref_1266_ = lean_ctor_get(v___y_1249_, 5);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_a_1265_);
lean_ctor_set(v___x_1262_, 0, v___x_1267_);
v___x_1269_ = v___x_1262_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_a_1265_);
v___x_1269_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
lean_ctor_set(v___x_1271_, 2, v___x_1270_);
lean_ctor_set(v___x_1271_, 3, v___x_1270_);
lean_ctor_set(v___x_1271_, 4, v___x_1270_);
lean_ctor_set(v___x_1271_, 5, v___x_1270_);
lean_inc(v_ref_1266_);
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_ref_1266_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1274_ = 4;
v___x_1275_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1240_, v___x_1271_, v___x_1272_, v___x_1273_, v___x_1270_, v___x_1274_, v___y_1249_, v___y_1245_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1283_);
v___x_1277_ = v___x_1275_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v___x_1275_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_diag_1260_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_diag_1260_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_diag_1260_);
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1275_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_del_object(v___x_1262_);
lean_dec_ref(v_diag_1260_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1245_);
lean_dec(v_tk_1240_);
v_a_1293_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1264_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1264_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v___y_1253_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1245_);
lean_dec(v_tk_1240_);
v_a_1302_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1257_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1257_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
v___jp_1310_:
{
uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = 0;
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
v___x_1327_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1313_, v___x_1325_, v___y_1312_, v___x_1325_, v___x_1326_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1313_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
if (lean_obj_tag(v___y_1315_) == 0)
{
lean_object* v_ctx_1329_; lean_object* v_simprocs_1330_; lean_object* v_dischargeWrapper_1331_; 
v_ctx_1329_ = lean_ctor_get(v_a_1328_, 0);
lean_inc_ref(v_ctx_1329_);
v_simprocs_1330_ = lean_ctor_get(v_a_1328_, 1);
lean_inc_ref(v_simprocs_1330_);
v_dischargeWrapper_1331_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_dischargeWrapper_1331_);
lean_dec(v_a_1328_);
v___y_1242_ = v_dischargeWrapper_1331_;
v___y_1243_ = v_simprocs_1330_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v___y_1324_;
v___y_1246_ = v___y_1318_;
v___y_1247_ = v___y_1320_;
v___y_1248_ = v___y_1319_;
v___y_1249_ = v___y_1323_;
v___y_1250_ = v___y_1321_;
v___y_1251_ = v_stxForSuggestion_1316_;
v___y_1252_ = v___y_1317_;
v___y_1253_ = v___y_1322_;
v___y_1254_ = v_ctx_1329_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v___y_1315_);
if (v___y_1314_ == 0)
{
lean_object* v_ctx_1332_; lean_object* v_simprocs_1333_; lean_object* v_dischargeWrapper_1334_; 
v_ctx_1332_ = lean_ctor_get(v_a_1328_, 0);
lean_inc_ref(v_ctx_1332_);
v_simprocs_1333_ = lean_ctor_get(v_a_1328_, 1);
lean_inc_ref(v_simprocs_1333_);
v_dischargeWrapper_1334_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_dischargeWrapper_1334_);
lean_dec(v_a_1328_);
v___y_1242_ = v_dischargeWrapper_1334_;
v___y_1243_ = v_simprocs_1333_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v___y_1324_;
v___y_1246_ = v___y_1318_;
v___y_1247_ = v___y_1320_;
v___y_1248_ = v___y_1319_;
v___y_1249_ = v___y_1323_;
v___y_1250_ = v___y_1321_;
v___y_1251_ = v_stxForSuggestion_1316_;
v___y_1252_ = v___y_1317_;
v___y_1253_ = v___y_1322_;
v___y_1254_ = v_ctx_1332_;
goto v___jp_1241_;
}
else
{
lean_object* v_ctx_1335_; lean_object* v_simprocs_1336_; lean_object* v_dischargeWrapper_1337_; lean_object* v___x_1338_; 
v_ctx_1335_ = lean_ctor_get(v_a_1328_, 0);
lean_inc_ref(v_ctx_1335_);
v_simprocs_1336_ = lean_ctor_get(v_a_1328_, 1);
lean_inc_ref(v_simprocs_1336_);
v_dischargeWrapper_1337_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_dischargeWrapper_1337_);
lean_dec(v_a_1328_);
v___x_1338_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1335_);
v___y_1242_ = v_dischargeWrapper_1337_;
v___y_1243_ = v_simprocs_1336_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v___y_1324_;
v___y_1246_ = v___y_1318_;
v___y_1247_ = v___y_1320_;
v___y_1248_ = v___y_1319_;
v___y_1249_ = v___y_1323_;
v___y_1250_ = v___y_1321_;
v___y_1251_ = v_stxForSuggestion_1316_;
v___y_1252_ = v___y_1317_;
v___y_1253_ = v___y_1322_;
v___y_1254_ = v___x_1338_;
goto v___jp_1241_;
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v_stxForSuggestion_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1311_);
lean_dec(v_tk_1240_);
v_a_1339_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1327_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1327_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
v___jp_1347_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = l_Array_append___redArg(v___y_1349_, v___y_1370_);
lean_dec_ref(v___y_1370_);
lean_inc(v___y_1364_);
v___x_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1372_, 0, v___y_1364_);
lean_ctor_set(v___x_1372_, 1, v___y_1356_);
lean_ctor_set(v___x_1372_, 2, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node6(v___y_1364_, v___y_1363_, v___y_1368_, v___y_1350_, v___y_1365_, v___y_1351_, v___y_1359_, v___x_1372_);
v___y_1311_ = v___y_1348_;
v___y_1312_ = v___y_1352_;
v___y_1313_ = v___y_1355_;
v___y_1314_ = v___y_1357_;
v___y_1315_ = v___y_1358_;
v_stxForSuggestion_1316_ = v___x_1373_;
v___y_1317_ = v___y_1362_;
v___y_1318_ = v___y_1366_;
v___y_1319_ = v___y_1360_;
v___y_1320_ = v___y_1369_;
v___y_1321_ = v___y_1367_;
v___y_1322_ = v___y_1354_;
v___y_1323_ = v___y_1353_;
v___y_1324_ = v___y_1361_;
goto v___jp_1310_;
}
v___jp_1374_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_inc_ref(v___y_1376_);
v___x_1398_ = l_Array_append___redArg(v___y_1376_, v___y_1397_);
lean_dec_ref(v___y_1397_);
lean_inc(v___y_1382_);
lean_inc(v___y_1390_);
v___x_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1390_);
lean_ctor_set(v___x_1399_, 1, v___y_1382_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_1390_);
v___x_1401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1390_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1403_ = l_Lean_Syntax_SepArray_ofElems(v___x_1402_, v___y_1377_);
lean_dec_ref(v___y_1377_);
lean_inc_ref(v___y_1376_);
v___x_1404_ = l_Array_append___redArg(v___y_1376_, v___x_1403_);
lean_dec_ref(v___x_1403_);
lean_inc(v___y_1382_);
lean_inc(v___y_1390_);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1390_);
lean_ctor_set(v___x_1405_, 1, v___y_1382_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_1390_);
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1390_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
lean_inc(v___y_1382_);
lean_inc(v___y_1390_);
v___x_1408_ = l_Lean_Syntax_node3(v___y_1390_, v___y_1382_, v___x_1401_, v___x_1405_, v___x_1407_);
if (lean_obj_tag(v___y_1394_) == 1)
{
lean_object* v_val_1409_; lean_object* v___x_1410_; 
v_val_1409_ = lean_ctor_get(v___y_1394_, 0);
lean_inc(v_val_1409_);
lean_dec_ref(v___y_1394_);
v___x_1410_ = l_Array_mkArray1___redArg(v_val_1409_);
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___y_1376_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___x_1399_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1383_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___x_1408_;
v___y_1360_ = v___y_1386_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1390_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___x_1410_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v___y_1394_);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___y_1376_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___x_1399_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1383_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___x_1408_;
v___y_1360_ = v___y_1386_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1390_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___x_1411_;
goto v___jp_1347_;
}
}
v___jp_1412_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc_ref(v___y_1414_);
v___x_1436_ = l_Array_append___redArg(v___y_1414_, v___y_1435_);
lean_dec_ref(v___y_1435_);
lean_inc(v___y_1420_);
lean_inc(v___y_1429_);
v___x_1437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1429_);
lean_ctor_set(v___x_1437_, 1, v___y_1420_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
if (lean_obj_tag(v___y_1423_) == 1)
{
lean_object* v_val_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_val_1438_ = lean_ctor_get(v___y_1423_, 0);
lean_inc(v_val_1438_);
lean_dec_ref(v___y_1423_);
v___x_1439_ = l_Lean_SourceInfo_fromRef(v_val_1438_, v___x_1224_);
lean_dec(v_val_1438_);
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Array_mkArray1___redArg(v___x_1441_);
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1425_;
v___y_1387_ = v___y_1426_;
v___y_1388_ = v___y_1427_;
v___y_1389_ = v___y_1428_;
v___y_1390_ = v___y_1429_;
v___y_1391_ = v___x_1437_;
v___y_1392_ = v___y_1430_;
v___y_1393_ = v___y_1431_;
v___y_1394_ = v___y_1432_;
v___y_1395_ = v___y_1434_;
v___y_1396_ = v___y_1433_;
v___y_1397_ = v___x_1442_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1443_; 
lean_dec(v___y_1423_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1425_;
v___y_1387_ = v___y_1426_;
v___y_1388_ = v___y_1427_;
v___y_1389_ = v___y_1428_;
v___y_1390_ = v___y_1429_;
v___y_1391_ = v___x_1437_;
v___y_1392_ = v___y_1430_;
v___y_1393_ = v___y_1431_;
v___y_1394_ = v___y_1432_;
v___y_1395_ = v___y_1434_;
v___y_1396_ = v___y_1433_;
v___y_1397_ = v___x_1443_;
goto v___jp_1374_;
}
}
v___jp_1444_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = l_Array_append___redArg(v___y_1463_, v___y_1467_);
lean_dec_ref(v___y_1467_);
lean_inc(v___y_1452_);
v___x_1469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1469_, 0, v___y_1452_);
lean_ctor_set(v___x_1469_, 1, v___y_1447_);
lean_ctor_set(v___x_1469_, 2, v___x_1468_);
v___x_1470_ = l_Lean_Syntax_node6(v___y_1452_, v___y_1456_, v___y_1446_, v___y_1448_, v___y_1462_, v___y_1458_, v___y_1453_, v___x_1469_);
v___y_1311_ = v___y_1445_;
v___y_1312_ = v___y_1449_;
v___y_1313_ = v___y_1454_;
v___y_1314_ = v___y_1455_;
v___y_1315_ = v___y_1457_;
v_stxForSuggestion_1316_ = v___x_1470_;
v___y_1317_ = v___y_1461_;
v___y_1318_ = v___y_1464_;
v___y_1319_ = v___y_1459_;
v___y_1320_ = v___y_1466_;
v___y_1321_ = v___y_1465_;
v___y_1322_ = v___y_1451_;
v___y_1323_ = v___y_1450_;
v___y_1324_ = v___y_1460_;
goto v___jp_1310_;
}
v___jp_1471_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_inc_ref(v___y_1489_);
v___x_1495_ = l_Array_append___redArg(v___y_1489_, v___y_1494_);
lean_dec_ref(v___y_1494_);
lean_inc(v___y_1475_);
lean_inc(v___y_1480_);
v___x_1496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1480_);
lean_ctor_set(v___x_1496_, 1, v___y_1475_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_1480_);
v___x_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___y_1480_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1500_ = l_Lean_Syntax_SepArray_ofElems(v___x_1499_, v___y_1473_);
lean_dec_ref(v___y_1473_);
lean_inc_ref(v___y_1489_);
v___x_1501_ = l_Array_append___redArg(v___y_1489_, v___x_1500_);
lean_dec_ref(v___x_1500_);
lean_inc(v___y_1475_);
lean_inc(v___y_1480_);
v___x_1502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1480_);
lean_ctor_set(v___x_1502_, 1, v___y_1475_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_1480_);
v___x_1504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___y_1480_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
lean_inc(v___y_1475_);
lean_inc(v___y_1480_);
v___x_1505_ = l_Lean_Syntax_node3(v___y_1480_, v___y_1475_, v___x_1498_, v___x_1502_, v___x_1504_);
if (lean_obj_tag(v___y_1492_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1507_; 
v_val_1506_ = lean_ctor_get(v___y_1492_, 0);
lean_inc(v_val_1506_);
lean_dec_ref(v___y_1492_);
v___x_1507_ = l_Array_mkArray1___redArg(v_val_1506_);
v___y_1445_ = v___y_1472_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1477_;
v___y_1450_ = v___y_1478_;
v___y_1451_ = v___y_1479_;
v___y_1452_ = v___y_1480_;
v___y_1453_ = v___x_1505_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___x_1496_;
v___y_1459_ = v___y_1485_;
v___y_1460_ = v___y_1486_;
v___y_1461_ = v___y_1487_;
v___y_1462_ = v___y_1488_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___y_1493_;
v___y_1467_ = v___x_1507_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1508_; 
lean_dec(v___y_1492_);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1445_ = v___y_1472_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1477_;
v___y_1450_ = v___y_1478_;
v___y_1451_ = v___y_1479_;
v___y_1452_ = v___y_1480_;
v___y_1453_ = v___x_1505_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___x_1496_;
v___y_1459_ = v___y_1485_;
v___y_1460_ = v___y_1486_;
v___y_1461_ = v___y_1487_;
v___y_1462_ = v___y_1488_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___y_1493_;
v___y_1467_ = v___x_1508_;
goto v___jp_1444_;
}
}
v___jp_1509_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_inc_ref(v___y_1527_);
v___x_1533_ = l_Array_append___redArg(v___y_1527_, v___y_1532_);
lean_dec_ref(v___y_1532_);
lean_inc(v___y_1513_);
lean_inc(v___y_1518_);
v___x_1534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1518_);
lean_ctor_set(v___x_1534_, 1, v___y_1513_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
if (lean_obj_tag(v___y_1522_) == 1)
{
lean_object* v_val_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_val_1535_ = lean_ctor_get(v___y_1522_, 0);
lean_inc(v_val_1535_);
lean_dec_ref(v___y_1522_);
v___x_1536_ = l_Lean_SourceInfo_fromRef(v_val_1535_, v___x_1224_);
lean_dec(v_val_1535_);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Array_mkArray1___redArg(v___x_1538_);
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___y_1524_;
v___y_1486_ = v___y_1525_;
v___y_1487_ = v___y_1526_;
v___y_1488_ = v___x_1534_;
v___y_1489_ = v___y_1527_;
v___y_1490_ = v___y_1528_;
v___y_1491_ = v___y_1529_;
v___y_1492_ = v___y_1530_;
v___y_1493_ = v___y_1531_;
v___y_1494_ = v___x_1539_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v___y_1522_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___y_1524_;
v___y_1486_ = v___y_1525_;
v___y_1487_ = v___y_1526_;
v___y_1488_ = v___x_1534_;
v___y_1489_ = v___y_1527_;
v___y_1490_ = v___y_1528_;
v___y_1491_ = v___y_1529_;
v___y_1492_ = v___y_1530_;
v___y_1493_ = v___y_1531_;
v___y_1494_ = v___x_1540_;
goto v___jp_1471_;
}
}
v___jp_1541_:
{
lean_object* v_ref_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_ref_1561_ = lean_ctor_get(v___y_1545_, 5);
v___x_1562_ = l_Lean_SourceInfo_fromRef(v_ref_1561_, v___y_1560_);
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1564_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1563_);
v___x_1565_ = l_Lean_SourceInfo_fromRef(v_tk_1240_, v___x_1224_);
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1563_);
v___x_1567_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1568_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1553_) == 1)
{
lean_object* v_val_1569_; lean_object* v___x_1570_; 
v_val_1569_ = lean_ctor_get(v___y_1553_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v___y_1553_);
v___x_1570_ = l_Array_mkArray1___redArg(v_val_1569_);
v___y_1510_ = v___y_1542_;
v___y_1511_ = v___y_1543_;
v___y_1512_ = v___x_1566_;
v___y_1513_ = v___x_1567_;
v___y_1514_ = v___y_1544_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___x_1562_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1549_;
v___y_1521_ = v___x_1564_;
v___y_1522_ = v___y_1550_;
v___y_1523_ = v___y_1551_;
v___y_1524_ = v___y_1552_;
v___y_1525_ = v___y_1554_;
v___y_1526_ = v___y_1555_;
v___y_1527_ = v___x_1568_;
v___y_1528_ = v___y_1556_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___y_1558_;
v___y_1531_ = v___y_1559_;
v___y_1532_ = v___x_1570_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1571_; 
lean_dec(v___y_1553_);
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1510_ = v___y_1542_;
v___y_1511_ = v___y_1543_;
v___y_1512_ = v___x_1566_;
v___y_1513_ = v___x_1567_;
v___y_1514_ = v___y_1544_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___x_1562_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1549_;
v___y_1521_ = v___x_1564_;
v___y_1522_ = v___y_1550_;
v___y_1523_ = v___y_1551_;
v___y_1524_ = v___y_1552_;
v___y_1525_ = v___y_1554_;
v___y_1526_ = v___y_1555_;
v___y_1527_ = v___x_1568_;
v___y_1528_ = v___y_1556_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___y_1558_;
v___y_1531_ = v___y_1559_;
v___y_1532_ = v___x_1571_;
goto v___jp_1509_;
}
}
v___jp_1572_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1574_);
if (lean_obj_tag(v___y_1580_) == 0)
{
lean_object* v_a_1592_; uint8_t v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = 0;
v___y_1542_ = v___y_1573_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___y_1589_;
v___y_1546_ = v___y_1576_;
v___y_1547_ = v___y_1588_;
v___y_1548_ = v_stxForExecution_1582_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___y_1579_;
v___y_1551_ = v___y_1580_;
v___y_1552_ = v___y_1585_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1590_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1584_;
v___y_1557_ = v___y_1587_;
v___y_1558_ = v___y_1577_;
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___x_1593_;
goto v___jp_1541_;
}
else
{
if (v___y_1578_ == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1591_);
v___y_1542_ = v___y_1573_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v_a_1594_;
v___y_1545_ = v___y_1589_;
v___y_1546_ = v___y_1576_;
v___y_1547_ = v___y_1588_;
v___y_1548_ = v_stxForExecution_1582_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___y_1579_;
v___y_1551_ = v___y_1580_;
v___y_1552_ = v___y_1585_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1590_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1584_;
v___y_1557_ = v___y_1587_;
v___y_1558_ = v___y_1577_;
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___y_1578_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1595_; lean_object* v_ref_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_a_1595_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1591_);
v_ref_1596_ = lean_ctor_get(v___y_1589_, 5);
v___x_1597_ = 0;
v___x_1598_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1600_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1599_);
v___x_1601_ = l_Lean_SourceInfo_fromRef(v_tk_1240_, v___x_1224_);
v___x_1602_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1605_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1581_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1607_; 
v_val_1606_ = lean_ctor_get(v___y_1581_, 0);
lean_inc(v_val_1606_);
lean_dec_ref(v___y_1581_);
v___x_1607_ = l_Array_mkArray1___redArg(v_val_1606_);
v___y_1413_ = v___y_1573_;
v___y_1414_ = v___x_1605_;
v___y_1415_ = v___y_1575_;
v___y_1416_ = v_a_1595_;
v___y_1417_ = v___y_1576_;
v___y_1418_ = v___y_1589_;
v___y_1419_ = v___y_1588_;
v___y_1420_ = v___x_1604_;
v___y_1421_ = v_stxForExecution_1582_;
v___y_1422_ = v___y_1578_;
v___y_1423_ = v___y_1579_;
v___y_1424_ = v___y_1580_;
v___y_1425_ = v___y_1585_;
v___y_1426_ = v___y_1590_;
v___y_1427_ = v___y_1583_;
v___y_1428_ = v___x_1600_;
v___y_1429_ = v___x_1598_;
v___y_1430_ = v___y_1584_;
v___y_1431_ = v___y_1587_;
v___y_1432_ = v___y_1577_;
v___y_1433_ = v___x_1603_;
v___y_1434_ = v___y_1586_;
v___y_1435_ = v___x_1607_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1608_; 
lean_dec(v___y_1581_);
v___x_1608_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1413_ = v___y_1573_;
v___y_1414_ = v___x_1605_;
v___y_1415_ = v___y_1575_;
v___y_1416_ = v_a_1595_;
v___y_1417_ = v___y_1576_;
v___y_1418_ = v___y_1589_;
v___y_1419_ = v___y_1588_;
v___y_1420_ = v___x_1604_;
v___y_1421_ = v_stxForExecution_1582_;
v___y_1422_ = v___y_1578_;
v___y_1423_ = v___y_1579_;
v___y_1424_ = v___y_1580_;
v___y_1425_ = v___y_1585_;
v___y_1426_ = v___y_1590_;
v___y_1427_ = v___y_1583_;
v___y_1428_ = v___x_1600_;
v___y_1429_ = v___x_1598_;
v___y_1430_ = v___y_1584_;
v___y_1431_ = v___y_1587_;
v___y_1432_ = v___y_1577_;
v___y_1433_ = v___x_1603_;
v___y_1434_ = v___y_1586_;
v___y_1435_ = v___x_1608_;
goto v___jp_1412_;
}
}
}
}
v___jp_1609_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = l_Array_append___redArg(v___y_1617_, v___y_1635_);
lean_dec_ref(v___y_1635_);
lean_inc(v___y_1621_);
v___x_1637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1621_);
lean_ctor_set(v___x_1637_, 1, v___y_1613_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
lean_inc(v___y_1622_);
v___x_1638_ = l_Lean_Syntax_node6(v___y_1621_, v___y_1626_, v___y_1618_, v___y_1622_, v___y_1611_, v___y_1612_, v___y_1632_, v___x_1637_);
v___y_1573_ = v___y_1610_;
v___y_1574_ = v___y_1622_;
v___y_1575_ = v___y_1623_;
v___y_1576_ = v___y_1625_;
v___y_1577_ = v___y_1633_;
v___y_1578_ = v___y_1616_;
v___y_1579_ = v___y_1628_;
v___y_1580_ = v___y_1629_;
v___y_1581_ = v___y_1630_;
v_stxForExecution_1582_ = v___x_1638_;
v___y_1583_ = v___y_1624_;
v___y_1584_ = v___y_1615_;
v___y_1585_ = v___y_1631_;
v___y_1586_ = v___y_1627_;
v___y_1587_ = v___y_1619_;
v___y_1588_ = v___y_1614_;
v___y_1589_ = v___y_1634_;
v___y_1590_ = v___y_1620_;
goto v___jp_1572_;
}
v___jp_1639_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_inc_ref(v___y_1654_);
v___x_1664_ = l_Array_append___redArg(v___y_1654_, v___y_1663_);
lean_dec_ref(v___y_1663_);
lean_inc(v___y_1645_);
lean_inc(v___y_1661_);
v___x_1665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1661_);
lean_ctor_set(v___x_1665_, 1, v___y_1645_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_1661_);
v___x_1667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1661_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1669_ = l_Lean_Syntax_SepArray_ofElems(v___x_1668_, v___y_1643_);
lean_inc_ref(v___y_1654_);
v___x_1670_ = l_Array_append___redArg(v___y_1654_, v___x_1669_);
lean_dec_ref(v___x_1669_);
lean_inc(v___y_1645_);
lean_inc(v___y_1661_);
v___x_1671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1661_);
lean_ctor_set(v___x_1671_, 1, v___y_1645_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_1661_);
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1661_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
lean_inc(v___y_1645_);
lean_inc(v___y_1661_);
v___x_1674_ = l_Lean_Syntax_node3(v___y_1661_, v___y_1645_, v___x_1667_, v___x_1671_, v___x_1673_);
if (lean_obj_tag(v___y_1660_) == 1)
{
lean_object* v_val_1675_; lean_object* v___x_1676_; 
v_val_1675_ = lean_ctor_get(v___y_1660_, 0);
lean_inc(v_val_1675_);
v___x_1676_ = l_Array_mkArray1___redArg(v_val_1675_);
v___y_1610_ = v___y_1640_;
v___y_1611_ = v___y_1641_;
v___y_1612_ = v___x_1665_;
v___y_1613_ = v___y_1645_;
v___y_1614_ = v___y_1647_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___y_1654_;
v___y_1618_ = v___y_1656_;
v___y_1619_ = v___y_1657_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1661_;
v___y_1622_ = v___y_1642_;
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v___y_1646_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1653_;
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___x_1674_;
v___y_1633_ = v___y_1660_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___x_1676_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1610_ = v___y_1640_;
v___y_1611_ = v___y_1641_;
v___y_1612_ = v___x_1665_;
v___y_1613_ = v___y_1645_;
v___y_1614_ = v___y_1647_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___y_1654_;
v___y_1618_ = v___y_1656_;
v___y_1619_ = v___y_1657_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1661_;
v___y_1622_ = v___y_1642_;
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v___y_1646_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1653_;
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___x_1674_;
v___y_1633_ = v___y_1660_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___x_1677_;
goto v___jp_1609_;
}
}
v___jp_1678_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v___y_1690_);
v___x_1702_ = l_Array_append___redArg(v___y_1690_, v___y_1701_);
lean_dec_ref(v___y_1701_);
lean_inc(v___y_1683_);
lean_inc(v___y_1699_);
v___x_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1699_);
lean_ctor_set(v___x_1703_, 1, v___y_1683_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
if (lean_obj_tag(v___y_1692_) == 1)
{
lean_object* v_val_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_val_1704_ = lean_ctor_get(v___y_1692_, 0);
v___x_1705_ = l_Lean_SourceInfo_fromRef(v_val_1704_, v___x_1224_);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Array_mkArray1___redArg(v___x_1707_);
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___x_1703_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___y_1681_;
v___y_1644_ = v___y_1682_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1688_;
v___y_1651_ = v___y_1691_;
v___y_1652_ = v___y_1692_;
v___y_1653_ = v___y_1689_;
v___y_1654_ = v___y_1690_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1693_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___y_1699_;
v___y_1662_ = v___y_1700_;
v___y_1663_ = v___x_1708_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___x_1703_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___y_1681_;
v___y_1644_ = v___y_1682_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1688_;
v___y_1651_ = v___y_1691_;
v___y_1652_ = v___y_1692_;
v___y_1653_ = v___y_1689_;
v___y_1654_ = v___y_1690_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1693_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___y_1699_;
v___y_1662_ = v___y_1700_;
v___y_1663_ = v___x_1709_;
goto v___jp_1639_;
}
}
v___jp_1710_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = l_Array_append___redArg(v___y_1721_, v___y_1736_);
lean_dec_ref(v___y_1736_);
lean_inc(v___y_1712_);
v___x_1738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1712_);
lean_ctor_set(v___x_1738_, 1, v___y_1728_);
lean_ctor_set(v___x_1738_, 2, v___x_1737_);
lean_inc(v___y_1724_);
v___x_1739_ = l_Lean_Syntax_node6(v___y_1712_, v___y_1715_, v___y_1719_, v___y_1724_, v___y_1723_, v___y_1720_, v___y_1717_, v___x_1738_);
v___y_1573_ = v___y_1711_;
v___y_1574_ = v___y_1724_;
v___y_1575_ = v___y_1725_;
v___y_1576_ = v___y_1727_;
v___y_1577_ = v___y_1734_;
v___y_1578_ = v___y_1716_;
v___y_1579_ = v___y_1730_;
v___y_1580_ = v___y_1731_;
v___y_1581_ = v___y_1732_;
v_stxForExecution_1582_ = v___x_1739_;
v___y_1583_ = v___y_1726_;
v___y_1584_ = v___y_1714_;
v___y_1585_ = v___y_1733_;
v___y_1586_ = v___y_1729_;
v___y_1587_ = v___y_1718_;
v___y_1588_ = v___y_1713_;
v___y_1589_ = v___y_1735_;
v___y_1590_ = v___y_1722_;
goto v___jp_1572_;
}
v___jp_1740_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc_ref(v___y_1759_);
v___x_1765_ = l_Array_append___redArg(v___y_1759_, v___y_1764_);
lean_dec_ref(v___y_1764_);
lean_inc(v___y_1750_);
lean_inc(v___y_1745_);
v___x_1766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1745_);
lean_ctor_set(v___x_1766_, 1, v___y_1750_);
lean_ctor_set(v___x_1766_, 2, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_1745_);
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___y_1745_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1770_ = l_Lean_Syntax_SepArray_ofElems(v___x_1769_, v___y_1743_);
lean_inc_ref(v___y_1759_);
v___x_1771_ = l_Array_append___redArg(v___y_1759_, v___x_1770_);
lean_dec_ref(v___x_1770_);
lean_inc(v___y_1750_);
lean_inc(v___y_1745_);
v___x_1772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1772_, 0, v___y_1745_);
lean_ctor_set(v___x_1772_, 1, v___y_1750_);
lean_ctor_set(v___x_1772_, 2, v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_1745_);
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___y_1745_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
lean_inc(v___y_1750_);
lean_inc(v___y_1745_);
v___x_1775_ = l_Lean_Syntax_node3(v___y_1745_, v___y_1750_, v___x_1768_, v___x_1772_, v___x_1774_);
if (lean_obj_tag(v___y_1761_) == 1)
{
lean_object* v_val_1776_; lean_object* v___x_1777_; 
v_val_1776_ = lean_ctor_get(v___y_1761_, 0);
lean_inc(v_val_1776_);
v___x_1777_ = l_Array_mkArray1___redArg(v_val_1776_);
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1745_;
v___y_1713_ = v___y_1747_;
v___y_1714_ = v___y_1748_;
v___y_1715_ = v___y_1749_;
v___y_1716_ = v___y_1751_;
v___y_1717_ = v___x_1775_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___x_1766_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1760_;
v___y_1723_ = v___y_1763_;
v___y_1724_ = v___y_1742_;
v___y_1725_ = v___y_1743_;
v___y_1726_ = v___y_1744_;
v___y_1727_ = v___y_1746_;
v___y_1728_ = v___y_1750_;
v___y_1729_ = v___y_1754_;
v___y_1730_ = v___y_1753_;
v___y_1731_ = v___y_1752_;
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___x_1777_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1745_;
v___y_1713_ = v___y_1747_;
v___y_1714_ = v___y_1748_;
v___y_1715_ = v___y_1749_;
v___y_1716_ = v___y_1751_;
v___y_1717_ = v___x_1775_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___x_1766_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1760_;
v___y_1723_ = v___y_1763_;
v___y_1724_ = v___y_1742_;
v___y_1725_ = v___y_1743_;
v___y_1726_ = v___y_1744_;
v___y_1727_ = v___y_1746_;
v___y_1728_ = v___y_1750_;
v___y_1729_ = v___y_1754_;
v___y_1730_ = v___y_1753_;
v___y_1731_ = v___y_1752_;
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___x_1778_;
goto v___jp_1710_;
}
}
v___jp_1779_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_inc_ref(v___y_1798_);
v___x_1803_ = l_Array_append___redArg(v___y_1798_, v___y_1802_);
lean_dec_ref(v___y_1802_);
lean_inc(v___y_1789_);
lean_inc(v___y_1783_);
v___x_1804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1783_);
lean_ctor_set(v___x_1804_, 1, v___y_1789_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
if (lean_obj_tag(v___y_1793_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_val_1805_ = lean_ctor_get(v___y_1793_, 0);
v___x_1806_ = l_Lean_SourceInfo_fromRef(v_val_1805_, v___x_1224_);
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Array_mkArray1___redArg(v___x_1808_);
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1784_;
v___y_1745_ = v___y_1783_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1792_;
v___y_1753_ = v___y_1793_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___y_1794_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1796_;
v___y_1758_ = v___y_1797_;
v___y_1759_ = v___y_1798_;
v___y_1760_ = v___y_1799_;
v___y_1761_ = v___y_1800_;
v___y_1762_ = v___y_1801_;
v___y_1763_ = v___x_1804_;
v___y_1764_ = v___x_1809_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1784_;
v___y_1745_ = v___y_1783_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1792_;
v___y_1753_ = v___y_1793_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___y_1794_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1796_;
v___y_1758_ = v___y_1797_;
v___y_1759_ = v___y_1798_;
v___y_1760_ = v___y_1799_;
v___y_1761_ = v___y_1800_;
v___y_1762_ = v___y_1801_;
v___y_1763_ = v___x_1804_;
v___y_1764_ = v___x_1810_;
goto v___jp_1740_;
}
}
v___jp_1811_:
{
lean_object* v_ref_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_ref_1830_ = lean_ctor_get(v___y_1828_, 5);
v___x_1831_ = l_Lean_SourceInfo_fromRef(v_ref_1830_, v___y_1829_);
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc_ref(v___x_1225_);
v___x_1833_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1832_);
v___x_1834_ = l_Lean_SourceInfo_fromRef(v_tk_1240_, v___x_1224_);
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1832_);
v___x_1836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1837_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1823_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1839_; 
v_val_1838_ = lean_ctor_get(v___y_1823_, 0);
lean_inc(v_val_1838_);
v___x_1839_ = l_Array_mkArray1___redArg(v_val_1838_);
v___y_1780_ = v___y_1812_;
v___y_1781_ = v___y_1813_;
v___y_1782_ = v___y_1814_;
v___y_1783_ = v___x_1831_;
v___y_1784_ = v___y_1815_;
v___y_1785_ = v___y_1816_;
v___y_1786_ = v___y_1817_;
v___y_1787_ = v___y_1818_;
v___y_1788_ = v___x_1833_;
v___y_1789_ = v___x_1836_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1822_;
v___y_1794_ = v___y_1823_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___x_1835_;
v___y_1797_ = v___y_1825_;
v___y_1798_ = v___x_1837_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1827_;
v___y_1801_ = v___y_1828_;
v___y_1802_ = v___x_1839_;
goto v___jp_1779_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1780_ = v___y_1812_;
v___y_1781_ = v___y_1813_;
v___y_1782_ = v___y_1814_;
v___y_1783_ = v___x_1831_;
v___y_1784_ = v___y_1815_;
v___y_1785_ = v___y_1816_;
v___y_1786_ = v___y_1817_;
v___y_1787_ = v___y_1818_;
v___y_1788_ = v___x_1833_;
v___y_1789_ = v___x_1836_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1822_;
v___y_1794_ = v___y_1823_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___x_1835_;
v___y_1797_ = v___y_1825_;
v___y_1798_ = v___x_1837_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1827_;
v___y_1801_ = v___y_1828_;
v___y_1802_ = v___x_1840_;
goto v___jp_1779_;
}
}
v___jp_1841_:
{
if (lean_obj_tag(v___y_1847_) == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = 0;
v___y_1812_ = v___y_1842_;
v___y_1813_ = v___y_1843_;
v___y_1814_ = v_argsArray_1850_;
v___y_1815_ = v___y_1851_;
v___y_1816_ = v___y_1844_;
v___y_1817_ = v___y_1856_;
v___y_1818_ = v___y_1852_;
v___y_1819_ = v___y_1846_;
v___y_1820_ = v___y_1854_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1855_;
v___y_1825_ = v___y_1853_;
v___y_1826_ = v___y_1858_;
v___y_1827_ = v___y_1845_;
v___y_1828_ = v___y_1857_;
v___y_1829_ = v___x_1859_;
goto v___jp_1811_;
}
else
{
if (v___y_1846_ == 0)
{
v___y_1812_ = v___y_1842_;
v___y_1813_ = v___y_1843_;
v___y_1814_ = v_argsArray_1850_;
v___y_1815_ = v___y_1851_;
v___y_1816_ = v___y_1844_;
v___y_1817_ = v___y_1856_;
v___y_1818_ = v___y_1852_;
v___y_1819_ = v___y_1846_;
v___y_1820_ = v___y_1854_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1855_;
v___y_1825_ = v___y_1853_;
v___y_1826_ = v___y_1858_;
v___y_1827_ = v___y_1845_;
v___y_1828_ = v___y_1857_;
v___y_1829_ = v___y_1846_;
goto v___jp_1811_;
}
else
{
lean_object* v_ref_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_ref_1860_ = lean_ctor_get(v___y_1857_, 5);
v___x_1861_ = 0;
v___x_1862_ = l_Lean_SourceInfo_fromRef(v_ref_1860_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc_ref(v___x_1225_);
v___x_1864_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1863_);
v___x_1865_ = l_Lean_SourceInfo_fromRef(v_tk_1240_, v___x_1224_);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1869_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1849_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1871_; 
v_val_1870_ = lean_ctor_get(v___y_1849_, 0);
lean_inc(v_val_1870_);
v___x_1871_ = l_Array_mkArray1___redArg(v_val_1870_);
v___y_1679_ = v___y_1842_;
v___y_1680_ = v___y_1843_;
v___y_1681_ = v_argsArray_1850_;
v___y_1682_ = v___y_1851_;
v___y_1683_ = v___x_1868_;
v___y_1684_ = v___y_1844_;
v___y_1685_ = v___y_1856_;
v___y_1686_ = v___x_1864_;
v___y_1687_ = v___y_1852_;
v___y_1688_ = v___y_1846_;
v___y_1689_ = v___y_1854_;
v___y_1690_ = v___x_1869_;
v___y_1691_ = v___y_1847_;
v___y_1692_ = v___y_1848_;
v___y_1693_ = v___x_1867_;
v___y_1694_ = v___y_1849_;
v___y_1695_ = v___y_1855_;
v___y_1696_ = v___y_1853_;
v___y_1697_ = v___y_1858_;
v___y_1698_ = v___y_1845_;
v___y_1699_ = v___x_1862_;
v___y_1700_ = v___y_1857_;
v___y_1701_ = v___x_1871_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1679_ = v___y_1842_;
v___y_1680_ = v___y_1843_;
v___y_1681_ = v_argsArray_1850_;
v___y_1682_ = v___y_1851_;
v___y_1683_ = v___x_1868_;
v___y_1684_ = v___y_1844_;
v___y_1685_ = v___y_1856_;
v___y_1686_ = v___x_1864_;
v___y_1687_ = v___y_1852_;
v___y_1688_ = v___y_1846_;
v___y_1689_ = v___y_1854_;
v___y_1690_ = v___x_1869_;
v___y_1691_ = v___y_1847_;
v___y_1692_ = v___y_1848_;
v___y_1693_ = v___x_1867_;
v___y_1694_ = v___y_1849_;
v___y_1695_ = v___y_1855_;
v___y_1696_ = v___y_1853_;
v___y_1697_ = v___y_1858_;
v___y_1698_ = v___y_1845_;
v___y_1699_ = v___x_1862_;
v___y_1700_ = v___y_1857_;
v___y_1701_ = v___x_1872_;
goto v___jp_1678_;
}
}
}
}
v___jp_1873_:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1876_, v___y_1889_, v___y_1879_, v___y_1885_, v___y_1884_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1889_);
v___x_1894_ = l_Lean_LibrarySuggestions_select(v_a_1893_, v___y_1891_, v___y_1889_, v___y_1879_, v___y_1885_, v___y_1884_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; size_t v_sz_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
v_sz_1896_ = lean_array_size(v_a_1895_);
v___x_1897_ = ((size_t)0ULL);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1890_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1895_, v_sz_1896_, v___x_1897_, v___y_1887_, v___y_1890_, v___y_1876_, v___y_1883_, v___y_1886_, v___y_1889_, v___y_1879_, v___y_1885_, v___y_1884_);
lean_dec(v_a_1895_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___y_1842_ = v___y_1874_;
v___y_1843_ = v___y_1875_;
v___y_1844_ = v___y_1877_;
v___y_1845_ = v___y_1888_;
v___y_1846_ = v___y_1878_;
v___y_1847_ = v___y_1881_;
v___y_1848_ = v___y_1880_;
v___y_1849_ = v___y_1882_;
v_argsArray_1850_ = v_a_1899_;
v___y_1851_ = v___y_1890_;
v___y_1852_ = v___y_1876_;
v___y_1853_ = v___y_1883_;
v___y_1854_ = v___y_1886_;
v___y_1855_ = v___y_1889_;
v___y_1856_ = v___y_1879_;
v___y_1857_ = v___y_1885_;
v___y_1858_ = v___y_1884_;
goto v___jp_1841_;
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v_a_1900_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v_a_1908_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1894_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1894_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v_a_1916_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1892_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1892_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
v___jp_1924_:
{
uint8_t v_suggestions_1943_; 
v_suggestions_1943_ = lean_ctor_get_uint8(v___y_1929_, sizeof(void*)*3 + 26);
if (v_suggestions_1943_ == 0)
{
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___f_1228_);
v___y_1842_ = v___y_1925_;
v___y_1843_ = v___y_1926_;
v___y_1844_ = v___y_1928_;
v___y_1845_ = v___y_1939_;
v___y_1846_ = v___y_1930_;
v___y_1847_ = v___y_1933_;
v___y_1848_ = v___y_1932_;
v___y_1849_ = v___y_1934_;
v_argsArray_1850_ = v___y_1942_;
v___y_1851_ = v___y_1941_;
v___y_1852_ = v___y_1927_;
v___y_1853_ = v___y_1935_;
v___y_1854_ = v___y_1938_;
v___y_1855_ = v___y_1940_;
v___y_1856_ = v___y_1931_;
v___y_1857_ = v___y_1937_;
v___y_1858_ = v___y_1936_;
goto v___jp_1841_;
}
else
{
lean_object* v_maxSuggestions_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_maxSuggestions_1944_ = lean_ctor_get(v___y_1929_, 2);
lean_inc(v_maxSuggestions_1944_);
lean_dec_ref(v___y_1929_);
v___x_1945_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1946_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1944_) == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_unsigned_to_nat(100u);
v___x_1948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1945_);
lean_ctor_set(v___x_1948_, 2, v___f_1228_);
lean_ctor_set(v___x_1948_, 3, v___x_1946_);
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1930_;
v___y_1879_ = v___y_1931_;
v___y_1880_ = v___y_1932_;
v___y_1881_ = v___y_1933_;
v___y_1882_ = v___y_1934_;
v___y_1883_ = v___y_1935_;
v___y_1884_ = v___y_1936_;
v___y_1885_ = v___y_1937_;
v___y_1886_ = v___y_1938_;
v___y_1887_ = v___y_1942_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___y_1940_;
v___y_1890_ = v___y_1941_;
v___y_1891_ = v___x_1948_;
goto v___jp_1873_;
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1950_; 
v_val_1949_ = lean_ctor_get(v_maxSuggestions_1944_, 0);
lean_inc(v_val_1949_);
lean_dec_ref(v_maxSuggestions_1944_);
v___x_1950_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1950_, 0, v_val_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1945_);
lean_ctor_set(v___x_1950_, 2, v___f_1228_);
lean_ctor_set(v___x_1950_, 3, v___x_1946_);
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1930_;
v___y_1879_ = v___y_1931_;
v___y_1880_ = v___y_1932_;
v___y_1881_ = v___y_1933_;
v___y_1882_ = v___y_1934_;
v___y_1883_ = v___y_1935_;
v___y_1884_ = v___y_1936_;
v___y_1885_ = v___y_1937_;
v___y_1886_ = v___y_1938_;
v___y_1887_ = v___y_1942_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___y_1940_;
v___y_1890_ = v___y_1941_;
v___y_1891_ = v___x_1950_;
goto v___jp_1873_;
}
}
}
v___jp_1951_:
{
uint8_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = 0;
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1958_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1956_);
v___x_1968_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1956_, v___x_1967_, v___y_1960_, v___y_1965_, v___y_1963_, v___y_1958_, v___y_1957_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1968_) == 0)
{
if (lean_obj_tag(v___y_1955_) == 1)
{
lean_object* v_a_1969_; lean_object* v_val_1970_; lean_object* v___x_1971_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v_val_1970_ = lean_ctor_get(v___y_1955_, 0);
lean_inc(v_val_1970_);
lean_dec_ref(v___y_1955_);
v___x_1971_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1970_);
lean_dec(v_val_1970_);
lean_inc(v___y_1959_);
v___y_1925_ = v___y_1959_;
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1962_;
v___y_1928_ = v___x_1967_;
v___y_1929_ = v_a_1969_;
v___y_1930_ = v___y_1952_;
v___y_1931_ = v___y_1957_;
v___y_1932_ = v___y_1964_;
v___y_1933_ = v___y_1961_;
v___y_1934_ = v___y_1966_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1954_;
v___y_1937_ = v___y_1953_;
v___y_1938_ = v___y_1963_;
v___y_1939_ = v___y_1959_;
v___y_1940_ = v___y_1958_;
v___y_1941_ = v___y_1960_;
v___y_1942_ = v___x_1971_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
lean_dec(v___y_1955_);
v_a_1972_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1968_);
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1959_);
v___y_1925_ = v___y_1959_;
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1962_;
v___y_1928_ = v___x_1967_;
v___y_1929_ = v_a_1972_;
v___y_1930_ = v___y_1952_;
v___y_1931_ = v___y_1957_;
v___y_1932_ = v___y_1964_;
v___y_1933_ = v___y_1961_;
v___y_1934_ = v___y_1966_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1954_;
v___y_1937_ = v___y_1953_;
v___y_1938_ = v___y_1963_;
v___y_1939_ = v___y_1959_;
v___y_1940_ = v___y_1958_;
v___y_1941_ = v___y_1960_;
v___y_1942_ = v___x_1973_;
goto v___jp_1924_;
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v_a_1974_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1968_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1968_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
v___jp_1982_:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Syntax_getOptional_x3f(v___y_1991_);
lean_dec(v___y_1991_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_box(0);
v___y_1952_ = v___y_1986_;
v___y_1953_ = v___y_1993_;
v___y_1954_ = v___y_1992_;
v___y_1955_ = v___y_1984_;
v___y_1956_ = v___y_1983_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1995_;
v___y_1959_ = v___y_1997_;
v___y_1960_ = v___y_1996_;
v___y_1961_ = v___y_1988_;
v___y_1962_ = v___y_1985_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___x_1999_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_val_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v___y_1952_ = v___y_1986_;
v___y_1953_ = v___y_1993_;
v___y_1954_ = v___y_1992_;
v___y_1955_ = v___y_1984_;
v___y_1956_ = v___y_1983_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1995_;
v___y_1959_ = v___y_1997_;
v___y_1960_ = v___y_1996_;
v___y_1961_ = v___y_1988_;
v___y_1962_ = v___y_1985_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___x_2005_;
goto v___jp_1951_;
}
}
}
}
v___jp_2008_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(4u);
v___x_2025_ = l_Lean_Syntax_getArg(v___y_2011_, v___x_2024_);
lean_dec(v___y_2011_);
v___x_2026_ = l_Lean_Syntax_getOptional_x3f(v___x_2025_);
lean_dec(v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_box(0);
v___y_1983_ = v___y_2009_;
v___y_1984_ = v_args_2015_;
v___y_1985_ = v___y_2017_;
v___y_1986_ = v___y_2012_;
v___y_1987_ = v___y_2021_;
v___y_1988_ = v___y_2014_;
v___y_1989_ = v___y_2013_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2010_;
v___y_1992_ = v___y_2023_;
v___y_1993_ = v___y_2022_;
v___y_1994_ = v___y_2019_;
v___y_1995_ = v___y_2020_;
v___y_1996_ = v___y_2016_;
v___y_1997_ = v___x_2027_;
goto v___jp_1982_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_val_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_val_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v___y_1983_ = v___y_2009_;
v___y_1984_ = v_args_2015_;
v___y_1985_ = v___y_2017_;
v___y_1986_ = v___y_2012_;
v___y_1987_ = v___y_2021_;
v___y_1988_ = v___y_2014_;
v___y_1989_ = v___y_2013_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2010_;
v___y_1992_ = v___y_2023_;
v___y_1993_ = v___y_2022_;
v___y_1994_ = v___y_2019_;
v___y_1995_ = v___y_2020_;
v___y_1996_ = v___y_2016_;
v___y_1997_ = v___x_2033_;
goto v___jp_1982_;
}
}
}
}
v___jp_2037_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = lean_unsigned_to_nat(3u);
v___x_2053_ = l_Lean_Syntax_getArg(v___y_2041_, v___x_2052_);
v___x_2054_ = l_Lean_Syntax_isNone(v___x_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
lean_inc(v___x_2053_);
v___x_2055_ = l_Lean_Syntax_matchesNull(v___x_2053_, v___x_2036_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v___x_2053_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v_o_2043_);
lean_dec(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = l_Lean_Syntax_getArg(v___x_2053_, v___x_1239_);
lean_dec(v___x_2053_);
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc_ref(v___x_1225_);
v___x_2059_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_2058_);
lean_inc(v___x_2057_);
v___x_2060_ = l_Lean_Syntax_isOfKind(v___x_2057_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec(v___x_2057_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v_o_2043_);
lean_dec(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v_args_2063_; lean_object* v___x_2064_; 
v___x_2062_ = l_Lean_Syntax_getArg(v___x_2057_, v___x_2036_);
lean_dec(v___x_2057_);
v_args_2063_ = l_Lean_Syntax_getArgs(v___x_2062_);
lean_dec(v___x_2062_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_args_2063_);
v___y_2009_ = v___y_2038_;
v___y_2010_ = v___y_2039_;
v___y_2011_ = v___y_2041_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v_o_2043_;
v___y_2014_ = v___y_2042_;
v_args_2015_ = v___x_2064_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v___y_2019_ = v___y_2047_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2051_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2065_; 
lean_dec(v___x_2053_);
v___x_2065_ = lean_box(0);
v___y_2009_ = v___y_2038_;
v___y_2010_ = v___y_2039_;
v___y_2011_ = v___y_2041_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v_o_2043_;
v___y_2014_ = v___y_2042_;
v_args_2015_ = v___x_2065_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v___y_2019_ = v___y_2047_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2051_;
goto v___jp_2008_;
}
}
v___jp_2066_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2076_ = lean_unsigned_to_nat(2u);
v___x_2077_ = l_Lean_Syntax_getArg(v_stx_1223_, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc_ref(v___x_1225_);
v___x_2079_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_2078_);
lean_inc(v___x_2077_);
v___x_2080_ = l_Lean_Syntax_isOfKind(v___x_2077_, v___x_2079_);
lean_dec(v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v___x_2077_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v_bang_2067_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2081_;
}
else
{
lean_object* v_cfg_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_cfg_2082_ = l_Lean_Syntax_getArg(v___x_2077_, v___x_1239_);
v___x_2083_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc_ref(v___x_1225_);
v___x_2084_ = l_Lean_Name_mkStr4(v___x_1225_, v___x_1226_, v___x_1227_, v___x_2083_);
lean_inc(v_cfg_2082_);
v___x_2085_ = l_Lean_Syntax_isOfKind(v_cfg_2082_, v___x_2084_);
lean_dec(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v_cfg_2082_);
lean_dec(v___x_2077_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v_bang_2067_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = l_Lean_Syntax_getArg(v___x_2077_, v___x_2036_);
v___x_2088_ = l_Lean_Syntax_getArg(v___x_2077_, v___x_2076_);
v___x_2089_ = l_Lean_Syntax_isNone(v___x_2088_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; 
lean_inc(v___x_2088_);
v___x_2090_ = l_Lean_Syntax_matchesNull(v___x_2088_, v___x_2036_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v_cfg_2082_);
lean_dec(v___x_2077_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v_bang_2067_);
lean_dec(v_tk_1240_);
lean_dec_ref(v___f_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
v___x_2091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2091_;
}
else
{
lean_object* v_o_2092_; lean_object* v___x_2093_; 
v_o_2092_ = l_Lean_Syntax_getArg(v___x_2088_, v___x_1239_);
lean_dec(v___x_2088_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_o_2092_);
v___y_2038_ = v_cfg_2082_;
v___y_2039_ = v___x_2087_;
v___y_2040_ = v___x_2085_;
v___y_2041_ = v___x_2077_;
v___y_2042_ = v_bang_2067_;
v_o_2043_ = v___x_2093_;
v___y_2044_ = v___y_2068_;
v___y_2045_ = v___y_2069_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2071_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v___y_2075_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2094_; 
lean_dec(v___x_2088_);
v___x_2094_ = lean_box(0);
v___y_2038_ = v_cfg_2082_;
v___y_2039_ = v___x_2087_;
v___y_2040_ = v___x_2085_;
v___y_2041_ = v___x_2077_;
v___y_2042_ = v_bang_2067_;
v_o_2043_ = v___x_2094_;
v___y_2044_ = v___y_2068_;
v___y_2045_ = v___y_2069_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2071_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v___y_2075_;
goto v___jp_2037_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2102_, lean_object* v_stx_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v___f_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
uint8_t v___x_40539__boxed_2118_; uint8_t v___x_40540__boxed_2119_; lean_object* v_res_2120_; 
v___x_40539__boxed_2118_ = lean_unbox(v___x_2102_);
v___x_40540__boxed_2119_ = lean_unbox(v___x_2104_);
v_res_2120_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40539__boxed_2118_, v_stx_2103_, v___x_40540__boxed_2119_, v___x_2105_, v___x_2106_, v___x_2107_, v___f_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v_stx_2103_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; uint8_t v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___y_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2130_);
v___x_2144_ = l_Lean_Syntax_isOfKind(v_stx_2130_, v___x_2143_);
v___x_2145_ = 1;
v___f_2146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2147_ = lean_box(v___x_2144_);
v___x_2148_ = lean_box(v___x_2145_);
v___y_2149_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2149_, 0, v___x_2147_);
lean_closure_set(v___y_2149_, 1, v_stx_2130_);
lean_closure_set(v___y_2149_, 2, v___x_2148_);
lean_closure_set(v___y_2149_, 3, v___x_2140_);
lean_closure_set(v___y_2149_, 4, v___x_2141_);
lean_closure_set(v___y_2149_, 5, v___x_2142_);
lean_closure_set(v___y_2149_, 6, v___f_2146_);
v___x_2150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2150_, 0, v___y_2149_);
v___x_2151_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2150_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2163_, lean_object* v_as_2164_, lean_object* v_as_x27_2165_, lean_object* v_b_2166_, lean_object* v_a_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2163_, v_as_x27_2165_, v_b_2166_, v___y_2174_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2178_, lean_object* v_as_2179_, lean_object* v_as_x27_2180_, lean_object* v_b_2181_, lean_object* v_a_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2178_, v_as_2179_, v_as_x27_2180_, v_b_2181_, v_a_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v_as_2179_);
lean_dec(v___x_2178_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2193_, lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2194_, v_msg_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_ref_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2206_, v_ref_2207_, v_msg_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v_ref_2207_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b1_2219_, lean_object* v_ref_2220_, lean_object* v_constName_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_2220_, v_constName_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_ref_2233_, lean_object* v_constName_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_00_u03b1_2232_, v_ref_2233_, v_constName_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v_ref_2233_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b1_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_2246_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b1_2257_, lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(v_00_u03b1_2257_, v_msg_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(lean_object* v_opt_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v_opt_2269_, v___y_2276_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_opt_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(v_opt_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_opt_2280_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b1_2291_, lean_object* v_ref_2292_, lean_object* v_msg_2293_, lean_object* v_declHint_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_2292_, v_msg_2293_, v_declHint_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_ref_2306_, lean_object* v_msg_2307_, lean_object* v_declHint_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(v_00_u03b1_2305_, v_ref_2306_, v_msg_2307_, v_declHint_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_ref_2306_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(lean_object* v_msg_2319_, lean_object* v_declHint_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_2319_, v_declHint_2320_, v___y_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___boxed(lean_object* v_msg_2331_, lean_object* v_declHint_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(v_msg_2331_, v_declHint_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(lean_object* v_ref_2343_, lean_object* v_msgData_2344_, uint8_t v_severity_2345_, uint8_t v_isSilent_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_2343_, v_msgData_2344_, v_severity_2345_, v_isSilent_2346_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___boxed(lean_object* v_ref_2357_, lean_object* v_msgData_2358_, lean_object* v_severity_2359_, lean_object* v_isSilent_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v_severity_boxed_2370_; uint8_t v_isSilent_boxed_2371_; lean_object* v_res_2372_; 
v_severity_boxed_2370_ = lean_unbox(v_severity_2359_);
v_isSilent_boxed_2371_ = lean_unbox(v_isSilent_2360_);
v_res_2372_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(v_ref_2357_, v_msgData_2358_, v_severity_boxed_2370_, v_isSilent_boxed_2371_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_ref_2357_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2380_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2381_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2384_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2380_, v___x_2381_, v___x_2382_, v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2415_ = l_Lean_addBuiltinDeclarationRanges(v___x_2413_, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2418_, lean_object* v_as_x27_2419_, lean_object* v_b_2420_, lean_object* v___y_2421_){
_start:
{
if (lean_obj_tag(v_as_x27_2419_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_b_2420_);
return v___x_2423_;
}
else
{
lean_object* v_head_2424_; lean_object* v_tail_2425_; lean_object* v_ref_2426_; uint8_t v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_head_2424_ = lean_ctor_get(v_as_x27_2419_, 0);
lean_inc(v_head_2424_);
v_tail_2425_ = lean_ctor_get(v_as_x27_2419_, 1);
lean_inc(v_tail_2425_);
lean_dec_ref(v_as_x27_2419_);
v_ref_2426_ = lean_ctor_get(v___y_2421_, 5);
v___x_2427_ = 1;
v___x_2428_ = 0;
v___x_2429_ = l_Lean_SourceInfo_fromRef(v_ref_2426_, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2431_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2432_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2429_);
v___x_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2429_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
lean_ctor_set(v___x_2433_, 2, v___x_2432_);
v___x_2434_ = l_Lean_mkCIdentFrom(v___x_2418_, v_head_2424_, v___x_2427_);
lean_inc_ref(v___x_2433_);
v___x_2435_ = l_Lean_Syntax_node3(v___x_2429_, v___x_2430_, v___x_2433_, v___x_2433_, v___x_2434_);
v___x_2436_ = lean_array_push(v_b_2420_, v___x_2435_);
v_as_x27_2419_ = v_tail_2425_;
v_b_2420_ = v___x_2436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2438_, lean_object* v_as_x27_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2438_, v_as_x27_2439_, v_b_2440_, v___y_2441_);
lean_dec_ref(v___y_2441_);
lean_dec(v___x_2438_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2444_, size_t v_sz_2445_, size_t v_i_2446_, lean_object* v_b_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_lt(v_i_2446_, v_sz_2445_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_b_2447_);
return v___x_2458_;
}
else
{
lean_object* v_a_2459_; lean_object* v_name_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2459_ = lean_array_uget_borrowed(v_as_2444_, v_i_2446_);
v_name_2460_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_name_2460_);
v___x_2461_ = lean_mk_syntax_ident(v_name_2460_);
lean_inc(v___y_2455_);
lean_inc_ref(v___y_2454_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___x_2461_);
v___x_2462_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2461_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2461_, v_a_2463_, v_b_2447_, v___y_2454_);
lean_dec(v___x_2461_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; size_t v___x_2466_; size_t v___x_2467_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2446_, v___x_2466_);
v_i_2446_ = v___x_2467_;
v_b_2447_ = v_a_2465_;
goto _start;
}
else
{
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v___x_2464_;
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v___x_2461_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v_b_2447_);
v_a_2469_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2462_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2462_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2477_, lean_object* v_sz_2478_, lean_object* v_i_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
size_t v_sz_boxed_2490_; size_t v_i_boxed_2491_; lean_object* v_res_2492_; 
v_sz_boxed_2490_ = lean_unbox_usize(v_sz_2478_);
lean_dec(v_sz_2478_);
v_i_boxed_2491_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_res_2492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2477_, v_sz_boxed_2490_, v_i_boxed_2491_, v_b_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec_ref(v_as_2477_);
return v_res_2492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_unsigned_to_nat(32u);
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2502_ = ((size_t)5ULL);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = lean_unsigned_to_nat(32u);
v___x_2505_ = lean_mk_empty_array_with_capacity(v___x_2504_);
v___x_2506_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2507_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2505_);
lean_ctor_set(v___x_2507_, 2, v___x_2503_);
lean_ctor_set(v___x_2507_, 3, v___x_2503_);
lean_ctor_set_usize(v___x_2507_, 4, v___x_2502_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2509_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
lean_ctor_set(v___x_2510_, 3, v___x_2508_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2512_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2522_, lean_object* v_stx_2523_, uint8_t v___x_2524_, lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v___x_2527_, lean_object* v___f_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
if (v___x_2522_ == 0)
{
lean_object* v___x_2538_; 
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_2538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2538_;
}
else
{
lean_object* v___x_2539_; lean_object* v_tk_2540_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2654_; uint8_t v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; lean_object* v_stxForSuggestion_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; uint8_t v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2740_; uint8_t v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; uint8_t v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2838_; uint8_t v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; uint8_t v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; uint8_t v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; uint8_t v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2893_; uint8_t v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2951_; uint8_t v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; uint8_t v___y_2966_; lean_object* v___y_2967_; uint8_t v___y_2968_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3000_; lean_object* v_stxForExecution_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; uint8_t v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; uint8_t v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3151_; lean_object* v___y_3152_; uint8_t v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; uint8_t v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; uint8_t v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; uint8_t v___y_3317_; uint8_t v___y_3318_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3348_; uint8_t v___y_3349_; lean_object* v_argsArray_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; uint8_t v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; uint8_t v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; uint8_t v___y_3484_; lean_object* v_args_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___x_3504_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v_o_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_bang_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_2539_ = lean_unsigned_to_nat(0u);
v_tk_2540_ = l_Lean_Syntax_getArg(v_stx_2523_, v___x_2539_);
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3563_ = l_Lean_Syntax_getArg(v_stx_2523_, v___x_3504_);
v___x_3564_ = l_Lean_Syntax_isNone(v___x_3563_);
if (v___x_3564_ == 0)
{
uint8_t v___x_3565_; 
lean_inc(v___x_3563_);
v___x_3565_ = l_Lean_Syntax_matchesNull(v___x_3563_, v___x_3504_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_dec(v___x_3563_);
lean_dec(v_tk_2540_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3566_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3566_;
}
else
{
lean_object* v_bang_3567_; lean_object* v___x_3568_; 
v_bang_3567_ = l_Lean_Syntax_getArg(v___x_3563_, v___x_2539_);
lean_dec(v___x_3563_);
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_bang_3567_);
v_bang_3535_ = v___x_3568_;
v___y_3536_ = v___y_2529_;
v___y_3537_ = v___y_2530_;
v___y_3538_ = v___y_2531_;
v___y_3539_ = v___y_2532_;
v___y_3540_ = v___y_2533_;
v___y_3541_ = v___y_2534_;
v___y_3542_ = v___y_2535_;
v___y_3543_ = v___y_2536_;
goto v___jp_3534_;
}
}
else
{
lean_object* v___x_3569_; 
lean_dec(v___x_3563_);
v___x_3569_ = lean_box(0);
v_bang_3535_ = v___x_3569_;
v___y_3536_ = v___y_2529_;
v___y_3537_ = v___y_2530_;
v___y_3538_ = v___y_2531_;
v___y_3539_ = v___y_2532_;
v___y_3540_ = v___y_2533_;
v___y_3541_ = v___y_2534_;
v___y_3542_ = v___y_2535_;
v___y_3543_ = v___y_2536_;
goto v___jp_3534_;
}
v___jp_2541_:
{
lean_object* v_usedTheorems_2548_; lean_object* v_diag_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2590_; 
v_usedTheorems_2548_ = lean_ctor_get(v___y_2542_, 0);
v_diag_2549_ = lean_ctor_get(v___y_2542_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___y_2542_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2551_ = v___y_2542_;
v_isShared_2552_ = v_isSharedCheck_2590_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_diag_2549_);
lean_inc(v_usedTheorems_2548_);
lean_dec(v___y_2542_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2590_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; 
lean_inc(v___y_2547_);
lean_inc_ref(v___y_2546_);
v___x_2553_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2543_, v_usedTheorems_2548_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec_ref(v_usedTheorems_2548_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v_ref_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v_ref_2555_ = lean_ctor_get(v___y_2546_, 5);
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 1, v_a_2554_);
lean_ctor_set(v___x_2551_, 0, v___x_2556_);
v___x_2558_ = v___x_2551_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_a_2554_);
v___x_2558_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
lean_ctor_set(v___x_2560_, 2, v___x_2559_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
lean_ctor_set(v___x_2560_, 4, v___x_2559_);
lean_ctor_set(v___x_2560_, 5, v___x_2559_);
lean_inc(v_ref_2555_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_ref_2555_);
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2563_ = 4;
v___x_2564_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2540_, v___x_2560_, v___x_2561_, v___x_2562_, v___x_2559_, v___x_2563_, v___y_2546_, v___y_2547_);
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
lean_ctor_set(v___x_2566_, 0, v_diag_2549_);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_diag_2549_);
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
lean_dec_ref(v_diag_2549_);
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
lean_del_object(v___x_2551_);
lean_dec_ref(v_diag_2549_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v_tk_2540_);
v_a_2582_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2553_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2553_);
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
v___x_2600_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2597_, v___y_2595_, v___y_2596_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
v___x_2603_ = l_Lean_Meta_simpAll(v_a_2601_, v___y_2599_, v___y_2598_, v___x_2602_, v___y_2595_, v___y_2596_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v_fst_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref(v___x_2603_);
v_fst_2605_ = lean_ctor_get(v_a_2604_, 0);
if (lean_obj_tag(v_fst_2605_) == 0)
{
lean_object* v_snd_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_snd_2606_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_a_2604_);
v___x_2607_ = lean_box(0);
v___x_2608_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2607_, v___y_2597_, v___y_2595_, v___y_2596_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2597_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_dec_ref(v___x_2608_);
v___y_2542_ = v_snd_2606_;
v___y_2543_ = v___y_2592_;
v___y_2544_ = v___y_2595_;
v___y_2545_ = v___y_2596_;
v___y_2546_ = v___y_2593_;
v___y_2547_ = v___y_2594_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_snd_2606_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v_tk_2540_);
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
lean_dec_ref(v_fst_2605_);
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
v___x_2625_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2624_, v___y_2597_, v___y_2595_, v___y_2596_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2597_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_dec_ref(v___x_2625_);
v___y_2542_ = v_snd_2617_;
v___y_2543_ = v___y_2592_;
v___y_2544_ = v___y_2595_;
v___y_2545_ = v___y_2596_;
v___y_2546_ = v___y_2593_;
v___y_2547_ = v___y_2594_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_snd_2617_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v_tk_2540_);
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
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v_tk_2540_);
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
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v_tk_2540_);
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
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v___y_2660_);
v___x_2668_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2657_, v___x_2524_, v___y_2655_, v___x_2524_, v___x_2667_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2657_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
if (lean_obj_tag(v___y_2654_) == 0)
{
lean_object* v_ctx_2670_; lean_object* v_simprocs_2671_; 
v_ctx_2670_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_ctx_2670_);
v_simprocs_2671_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_simprocs_2671_);
lean_dec(v_a_2669_);
v___y_2592_ = v_stxForSuggestion_2658_;
v___y_2593_ = v___y_2665_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2663_;
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2660_;
v___y_2598_ = v_simprocs_2671_;
v___y_2599_ = v_ctx_2670_;
goto v___jp_2591_;
}
else
{
lean_dec_ref(v___y_2654_);
if (v___y_2656_ == 0)
{
lean_object* v_ctx_2672_; lean_object* v_simprocs_2673_; 
v_ctx_2672_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_ctx_2672_);
v_simprocs_2673_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_simprocs_2673_);
lean_dec(v_a_2669_);
v___y_2592_ = v_stxForSuggestion_2658_;
v___y_2593_ = v___y_2665_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2663_;
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2660_;
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
v___y_2592_ = v_stxForSuggestion_2658_;
v___y_2593_ = v___y_2665_;
v___y_2594_ = v___y_2666_;
v___y_2595_ = v___y_2663_;
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2660_;
v___y_2598_ = v_simprocs_2675_;
v___y_2599_ = v___x_2676_;
goto v___jp_2591_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2660_);
lean_dec(v_stxForSuggestion_2658_);
lean_dec(v___y_2654_);
lean_dec(v_tk_2540_);
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
lean_inc_ref(v___y_2686_);
v___x_2706_ = l_Array_append___redArg(v___y_2686_, v___y_2705_);
lean_dec_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc(v___y_2692_);
v___x_2707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2692_);
lean_ctor_set(v___x_2707_, 1, v___y_2704_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
lean_inc(v___y_2692_);
v___x_2708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2708_, 0, v___y_2692_);
lean_ctor_set(v___x_2708_, 1, v___y_2704_);
lean_ctor_set(v___x_2708_, 2, v___y_2686_);
v___x_2709_ = l_Lean_Syntax_node5(v___y_2692_, v___y_2697_, v___y_2688_, v___y_2699_, v___y_2687_, v___x_2707_, v___x_2708_);
v___y_2654_ = v___y_2701_;
v___y_2655_ = v___y_2689_;
v___y_2656_ = v___y_2693_;
v___y_2657_ = v___y_2695_;
v_stxForSuggestion_2658_ = v___x_2709_;
v___y_2659_ = v___y_2694_;
v___y_2660_ = v___y_2690_;
v___y_2661_ = v___y_2702_;
v___y_2662_ = v___y_2703_;
v___y_2663_ = v___y_2696_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2691_;
v___y_2666_ = v___y_2698_;
goto v___jp_2653_;
}
v___jp_2710_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc_ref(v___y_2711_);
v___x_2731_ = l_Array_append___redArg(v___y_2711_, v___y_2730_);
lean_dec_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc(v___y_2716_);
v___x_2732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2732_, 0, v___y_2716_);
lean_ctor_set(v___x_2732_, 1, v___y_2729_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
if (lean_obj_tag(v___y_2713_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_val_2733_ = lean_ctor_get(v___y_2713_, 0);
lean_inc(v_val_2733_);
lean_dec_ref(v___y_2713_);
v___x_2734_ = l_Lean_SourceInfo_fromRef(v_val_2733_, v___x_2524_);
lean_dec(v_val_2733_);
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Array_mkArray1___redArg(v___x_2736_);
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___x_2732_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2717_;
v___y_2692_ = v___y_2716_;
v___y_2693_ = v___y_2718_;
v___y_2694_ = v___y_2719_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___y_2723_;
v___y_2699_ = v___y_2724_;
v___y_2700_ = v___y_2725_;
v___y_2701_ = v___y_2726_;
v___y_2702_ = v___y_2727_;
v___y_2703_ = v___y_2728_;
v___y_2704_ = v___y_2729_;
v___y_2705_ = v___x_2737_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v___y_2713_);
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___x_2732_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2717_;
v___y_2692_ = v___y_2716_;
v___y_2693_ = v___y_2718_;
v___y_2694_ = v___y_2719_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___y_2723_;
v___y_2699_ = v___y_2724_;
v___y_2700_ = v___y_2725_;
v___y_2701_ = v___y_2726_;
v___y_2702_ = v___y_2727_;
v___y_2703_ = v___y_2728_;
v___y_2704_ = v___y_2729_;
v___y_2705_ = v___x_2738_;
goto v___jp_2685_;
}
}
v___jp_2739_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_inc_ref(v___y_2740_);
v___x_2761_ = l_Array_append___redArg(v___y_2740_, v___y_2760_);
lean_dec_ref(v___y_2760_);
lean_inc(v___y_2746_);
lean_inc(v___y_2750_);
v___x_2762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2750_);
lean_ctor_set(v___x_2762_, 1, v___y_2746_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
v___x_2763_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_2750_);
v___x_2764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___y_2750_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2766_ = l_Lean_Syntax_SepArray_ofElems(v___x_2765_, v___y_2747_);
lean_dec_ref(v___y_2747_);
v___x_2767_ = l_Array_append___redArg(v___y_2740_, v___x_2766_);
lean_dec_ref(v___x_2766_);
lean_inc(v___y_2746_);
lean_inc(v___y_2750_);
v___x_2768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___y_2750_);
lean_ctor_set(v___x_2768_, 1, v___y_2746_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
v___x_2769_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_2750_);
v___x_2770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2750_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
lean_inc(v___y_2750_);
v___x_2771_ = l_Lean_Syntax_node3(v___y_2750_, v___y_2746_, v___x_2764_, v___x_2768_, v___x_2770_);
v___x_2772_ = l_Lean_Syntax_node5(v___y_2750_, v___y_2753_, v___y_2759_, v___y_2754_, v___y_2752_, v___x_2762_, v___x_2771_);
v___y_2654_ = v___y_2756_;
v___y_2655_ = v___y_2741_;
v___y_2656_ = v___y_2744_;
v___y_2657_ = v___y_2748_;
v_stxForSuggestion_2658_ = v___x_2772_;
v___y_2659_ = v___y_2745_;
v___y_2660_ = v___y_2742_;
v___y_2661_ = v___y_2757_;
v___y_2662_ = v___y_2758_;
v___y_2663_ = v___y_2749_;
v___y_2664_ = v___y_2755_;
v___y_2665_ = v___y_2743_;
v___y_2666_ = v___y_2751_;
goto v___jp_2653_;
}
v___jp_2773_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_inc_ref(v___y_2774_);
v___x_2795_ = l_Array_append___redArg(v___y_2774_, v___y_2794_);
lean_dec_ref(v___y_2794_);
lean_inc(v___y_2781_);
lean_inc(v___y_2785_);
v___x_2796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___y_2785_);
lean_ctor_set(v___x_2796_, 1, v___y_2781_);
lean_ctor_set(v___x_2796_, 2, v___x_2795_);
if (lean_obj_tag(v___y_2775_) == 1)
{
lean_object* v_val_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_val_2797_ = lean_ctor_get(v___y_2775_, 0);
lean_inc(v_val_2797_);
lean_dec_ref(v___y_2775_);
v___x_2798_ = l_Lean_SourceInfo_fromRef(v_val_2797_, v___x_2524_);
lean_dec(v_val_2797_);
v___x_2799_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Array_mkArray1___redArg(v___x_2800_);
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2783_;
v___y_2749_ = v___y_2784_;
v___y_2750_ = v___y_2785_;
v___y_2751_ = v___y_2786_;
v___y_2752_ = v___x_2796_;
v___y_2753_ = v___y_2787_;
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2789_;
v___y_2756_ = v___y_2790_;
v___y_2757_ = v___y_2791_;
v___y_2758_ = v___y_2792_;
v___y_2759_ = v___y_2793_;
v___y_2760_ = v___x_2801_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2802_; 
lean_dec(v___y_2775_);
v___x_2802_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2783_;
v___y_2749_ = v___y_2784_;
v___y_2750_ = v___y_2785_;
v___y_2751_ = v___y_2786_;
v___y_2752_ = v___x_2796_;
v___y_2753_ = v___y_2787_;
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2789_;
v___y_2756_ = v___y_2790_;
v___y_2757_ = v___y_2791_;
v___y_2758_ = v___y_2792_;
v___y_2759_ = v___y_2793_;
v___y_2760_ = v___x_2802_;
goto v___jp_2739_;
}
}
v___jp_2803_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_inc_ref(v___y_2812_);
v___x_2825_ = l_Array_append___redArg(v___y_2812_, v___y_2824_);
lean_dec_ref(v___y_2824_);
lean_inc(v___y_2815_);
lean_inc(v___y_2820_);
v___x_2826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2826_, 0, v___y_2820_);
lean_ctor_set(v___x_2826_, 1, v___y_2815_);
lean_ctor_set(v___x_2826_, 2, v___x_2825_);
v___x_2827_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_2820_);
v___x_2828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___y_2820_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2830_ = l_Lean_Syntax_SepArray_ofElems(v___x_2829_, v___y_2810_);
lean_dec_ref(v___y_2810_);
v___x_2831_ = l_Array_append___redArg(v___y_2812_, v___x_2830_);
lean_dec_ref(v___x_2830_);
lean_inc(v___y_2815_);
lean_inc(v___y_2820_);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___y_2820_);
lean_ctor_set(v___x_2832_, 1, v___y_2815_);
lean_ctor_set(v___x_2832_, 2, v___x_2831_);
v___x_2833_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_2820_);
v___x_2834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___y_2820_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
lean_inc(v___y_2820_);
v___x_2835_ = l_Lean_Syntax_node3(v___y_2820_, v___y_2815_, v___x_2828_, v___x_2832_, v___x_2834_);
v___x_2836_ = l_Lean_Syntax_node5(v___y_2820_, v___y_2805_, v___y_2818_, v___y_2816_, v___y_2823_, v___x_2826_, v___x_2835_);
v___y_2654_ = v___y_2819_;
v___y_2655_ = v___y_2804_;
v___y_2656_ = v___y_2808_;
v___y_2657_ = v___y_2811_;
v_stxForSuggestion_2658_ = v___x_2836_;
v___y_2659_ = v___y_2809_;
v___y_2660_ = v___y_2806_;
v___y_2661_ = v___y_2821_;
v___y_2662_ = v___y_2822_;
v___y_2663_ = v___y_2813_;
v___y_2664_ = v___y_2817_;
v___y_2665_ = v___y_2807_;
v___y_2666_ = v___y_2814_;
goto v___jp_2653_;
}
v___jp_2837_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc_ref(v___y_2846_);
v___x_2859_ = l_Array_append___redArg(v___y_2846_, v___y_2858_);
lean_dec_ref(v___y_2858_);
lean_inc(v___y_2849_);
lean_inc(v___y_2855_);
v___x_2860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2855_);
lean_ctor_set(v___x_2860_, 1, v___y_2849_);
lean_ctor_set(v___x_2860_, 2, v___x_2859_);
if (lean_obj_tag(v___y_2838_) == 1)
{
lean_object* v_val_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_val_2861_ = lean_ctor_get(v___y_2838_, 0);
lean_inc(v_val_2861_);
lean_dec_ref(v___y_2838_);
v___x_2862_ = l_Lean_SourceInfo_fromRef(v_val_2861_, v___x_2524_);
lean_dec(v_val_2861_);
v___x_2863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Array_mkArray1___redArg(v___x_2864_);
v___y_2804_ = v___y_2839_;
v___y_2805_ = v___y_2840_;
v___y_2806_ = v___y_2841_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2843_;
v___y_2809_ = v___y_2844_;
v___y_2810_ = v___y_2845_;
v___y_2811_ = v___y_2847_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2848_;
v___y_2814_ = v___y_2850_;
v___y_2815_ = v___y_2849_;
v___y_2816_ = v___y_2851_;
v___y_2817_ = v___y_2853_;
v___y_2818_ = v___y_2852_;
v___y_2819_ = v___y_2854_;
v___y_2820_ = v___y_2855_;
v___y_2821_ = v___y_2856_;
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v___x_2865_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2866_; 
lean_dec(v___y_2838_);
v___x_2866_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2804_ = v___y_2839_;
v___y_2805_ = v___y_2840_;
v___y_2806_ = v___y_2841_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2843_;
v___y_2809_ = v___y_2844_;
v___y_2810_ = v___y_2845_;
v___y_2811_ = v___y_2847_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2848_;
v___y_2814_ = v___y_2850_;
v___y_2815_ = v___y_2849_;
v___y_2816_ = v___y_2851_;
v___y_2817_ = v___y_2853_;
v___y_2818_ = v___y_2852_;
v___y_2819_ = v___y_2854_;
v___y_2820_ = v___y_2855_;
v___y_2821_ = v___y_2856_;
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v___x_2866_;
goto v___jp_2803_;
}
}
v___jp_2867_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_inc_ref(v___y_2869_);
v___x_2888_ = l_Array_append___redArg(v___y_2869_, v___y_2887_);
lean_dec_ref(v___y_2887_);
lean_inc(v___y_2872_);
lean_inc(v___y_2886_);
v___x_2889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2886_);
lean_ctor_set(v___x_2889_, 1, v___y_2872_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
lean_inc(v___y_2886_);
v___x_2890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___y_2886_);
lean_ctor_set(v___x_2890_, 1, v___y_2872_);
lean_ctor_set(v___x_2890_, 2, v___y_2869_);
v___x_2891_ = l_Lean_Syntax_node5(v___y_2886_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___x_2889_, v___x_2890_);
v___y_2654_ = v___y_2883_;
v___y_2655_ = v___y_2868_;
v___y_2656_ = v___y_2873_;
v___y_2657_ = v___y_2875_;
v_stxForSuggestion_2658_ = v___x_2891_;
v___y_2659_ = v___y_2874_;
v___y_2660_ = v___y_2870_;
v___y_2661_ = v___y_2884_;
v___y_2662_ = v___y_2885_;
v___y_2663_ = v___y_2876_;
v___y_2664_ = v___y_2882_;
v___y_2665_ = v___y_2871_;
v___y_2666_ = v___y_2877_;
goto v___jp_2653_;
}
v___jp_2892_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_inc_ref(v___y_2895_);
v___x_2913_ = l_Array_append___redArg(v___y_2895_, v___y_2912_);
lean_dec_ref(v___y_2912_);
lean_inc(v___y_2897_);
lean_inc(v___y_2911_);
v___x_2914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___y_2911_);
lean_ctor_set(v___x_2914_, 1, v___y_2897_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
if (lean_obj_tag(v___y_2893_) == 1)
{
lean_object* v_val_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_val_2915_ = lean_ctor_get(v___y_2893_, 0);
lean_inc(v_val_2915_);
lean_dec_ref(v___y_2893_);
v___x_2916_ = l_Lean_SourceInfo_fromRef(v_val_2915_, v___x_2524_);
lean_dec(v_val_2915_);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Array_mkArray1___redArg(v___x_2918_);
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2896_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2901_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___y_2906_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___x_2914_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2908_;
v___y_2884_ = v___y_2909_;
v___y_2885_ = v___y_2910_;
v___y_2886_ = v___y_2911_;
v___y_2887_ = v___x_2919_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2920_; 
lean_dec(v___y_2893_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2896_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2901_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___y_2906_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___x_2914_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2908_;
v___y_2884_ = v___y_2909_;
v___y_2885_ = v___y_2910_;
v___y_2886_ = v___y_2911_;
v___y_2887_ = v___x_2920_;
goto v___jp_2867_;
}
}
v___jp_2921_:
{
lean_object* v_ref_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_ref_2938_ = lean_ctor_get(v___y_2925_, 5);
v___x_2939_ = l_Lean_SourceInfo_fromRef(v_ref_2938_, v___y_2937_);
v___x_2940_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2941_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_2940_);
v___x_2942_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_2943_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2946_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2931_) == 1)
{
lean_object* v_val_2947_; lean_object* v___x_2948_; 
v_val_2947_ = lean_ctor_get(v___y_2931_, 0);
lean_inc(v_val_2947_);
lean_dec_ref(v___y_2931_);
v___x_2948_ = l_Array_mkArray1___redArg(v_val_2947_);
v___y_2711_ = v___x_2946_;
v___y_2712_ = v___x_2944_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2939_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2927_;
v___y_2720_ = v___y_2928_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___x_2941_;
v___y_2723_ = v___y_2930_;
v___y_2724_ = v___y_2932_;
v___y_2725_ = v___y_2933_;
v___y_2726_ = v___y_2934_;
v___y_2727_ = v___y_2935_;
v___y_2728_ = v___y_2936_;
v___y_2729_ = v___x_2945_;
v___y_2730_ = v___x_2948_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2949_; 
lean_dec(v___y_2931_);
v___x_2949_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2711_ = v___x_2946_;
v___y_2712_ = v___x_2944_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2939_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2927_;
v___y_2720_ = v___y_2928_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___x_2941_;
v___y_2723_ = v___y_2930_;
v___y_2724_ = v___y_2932_;
v___y_2725_ = v___y_2933_;
v___y_2726_ = v___y_2934_;
v___y_2727_ = v___y_2935_;
v___y_2728_ = v___y_2936_;
v___y_2729_ = v___x_2945_;
v___y_2730_ = v___x_2949_;
goto v___jp_2710_;
}
}
v___jp_2950_:
{
if (v___y_2968_ == 0)
{
lean_object* v_ref_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_ref_2969_ = lean_ctor_get(v___y_2954_, 5);
v___x_2970_ = l_Lean_SourceInfo_fromRef(v_ref_2969_, v___y_2968_);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2972_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_2971_);
v___x_2973_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2977_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2961_) == 1)
{
lean_object* v_val_2978_; lean_object* v___x_2979_; 
v_val_2978_ = lean_ctor_get(v___y_2961_, 0);
lean_inc(v_val_2978_);
lean_dec_ref(v___y_2961_);
v___x_2979_ = l_Array_mkArray1___redArg(v_val_2978_);
v___y_2774_ = v___x_2977_;
v___y_2775_ = v___y_2951_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___x_2976_;
v___y_2782_ = v___y_2957_;
v___y_2783_ = v___y_2958_;
v___y_2784_ = v___y_2959_;
v___y_2785_ = v___x_2970_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2972_;
v___y_2788_ = v___y_2962_;
v___y_2789_ = v___y_2963_;
v___y_2790_ = v___y_2964_;
v___y_2791_ = v___y_2965_;
v___y_2792_ = v___y_2967_;
v___y_2793_ = v___x_2975_;
v___y_2794_ = v___x_2979_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v___y_2961_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2774_ = v___x_2977_;
v___y_2775_ = v___y_2951_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___x_2976_;
v___y_2782_ = v___y_2957_;
v___y_2783_ = v___y_2958_;
v___y_2784_ = v___y_2959_;
v___y_2785_ = v___x_2970_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2972_;
v___y_2788_ = v___y_2962_;
v___y_2789_ = v___y_2963_;
v___y_2790_ = v___y_2964_;
v___y_2791_ = v___y_2965_;
v___y_2792_ = v___y_2967_;
v___y_2793_ = v___x_2975_;
v___y_2794_ = v___x_2980_;
goto v___jp_2773_;
}
}
else
{
lean_object* v_ref_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_ref_2981_ = lean_ctor_get(v___y_2954_, 5);
v___x_2982_ = l_Lean_SourceInfo_fromRef(v_ref_2981_, v___y_2966_);
v___x_2983_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2984_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_2983_);
v___x_2985_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2989_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2961_) == 1)
{
lean_object* v_val_2990_; lean_object* v___x_2991_; 
v_val_2990_ = lean_ctor_get(v___y_2961_, 0);
lean_inc(v_val_2990_);
lean_dec_ref(v___y_2961_);
v___x_2991_ = l_Array_mkArray1___redArg(v_val_2990_);
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___x_2984_;
v___y_2841_ = v___y_2953_;
v___y_2842_ = v___y_2954_;
v___y_2843_ = v___y_2955_;
v___y_2844_ = v___y_2956_;
v___y_2845_ = v___y_2957_;
v___y_2846_ = v___x_2989_;
v___y_2847_ = v___y_2958_;
v___y_2848_ = v___y_2959_;
v___y_2849_ = v___x_2988_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___y_2962_;
v___y_2852_ = v___x_2987_;
v___y_2853_ = v___y_2963_;
v___y_2854_ = v___y_2964_;
v___y_2855_ = v___x_2982_;
v___y_2856_ = v___y_2965_;
v___y_2857_ = v___y_2967_;
v___y_2858_ = v___x_2991_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v___y_2961_);
v___x_2992_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___x_2984_;
v___y_2841_ = v___y_2953_;
v___y_2842_ = v___y_2954_;
v___y_2843_ = v___y_2955_;
v___y_2844_ = v___y_2956_;
v___y_2845_ = v___y_2957_;
v___y_2846_ = v___x_2989_;
v___y_2847_ = v___y_2958_;
v___y_2848_ = v___y_2959_;
v___y_2849_ = v___x_2988_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___y_2962_;
v___y_2852_ = v___x_2987_;
v___y_2853_ = v___y_2963_;
v___y_2854_ = v___y_2964_;
v___y_2855_ = v___x_2982_;
v___y_2856_ = v___y_2965_;
v___y_2857_ = v___y_2967_;
v___y_2858_ = v___x_2992_;
goto v___jp_2837_;
}
}
}
v___jp_2993_:
{
lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3010_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2995_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = lean_array_get_size(v___y_3000_);
v___x_3013_ = lean_nat_dec_eq(v___x_3012_, v___x_2539_);
if (v___x_3013_ == 0)
{
if (lean_obj_tag(v___y_2996_) == 0)
{
v___y_2951_ = v___y_2997_;
v___y_2952_ = v___y_2998_;
v___y_2953_ = v___y_3003_;
v___y_2954_ = v___y_3008_;
v___y_2955_ = v___y_2999_;
v___y_2956_ = v___y_3002_;
v___y_2957_ = v___y_3000_;
v___y_2958_ = v_stxForExecution_3001_;
v___y_2959_ = v___y_3006_;
v___y_2960_ = v___y_3009_;
v___y_2961_ = v___y_2994_;
v___y_2962_ = v_a_3011_;
v___y_2963_ = v___y_3007_;
v___y_2964_ = v___y_2996_;
v___y_2965_ = v___y_3004_;
v___y_2966_ = v___x_3013_;
v___y_2967_ = v___y_3005_;
v___y_2968_ = v___x_3013_;
goto v___jp_2950_;
}
else
{
v___y_2951_ = v___y_2997_;
v___y_2952_ = v___y_2998_;
v___y_2953_ = v___y_3003_;
v___y_2954_ = v___y_3008_;
v___y_2955_ = v___y_2999_;
v___y_2956_ = v___y_3002_;
v___y_2957_ = v___y_3000_;
v___y_2958_ = v_stxForExecution_3001_;
v___y_2959_ = v___y_3006_;
v___y_2960_ = v___y_3009_;
v___y_2961_ = v___y_2994_;
v___y_2962_ = v_a_3011_;
v___y_2963_ = v___y_3007_;
v___y_2964_ = v___y_2996_;
v___y_2965_ = v___y_3004_;
v___y_2966_ = v___x_3013_;
v___y_2967_ = v___y_3005_;
v___y_2968_ = v___y_2999_;
goto v___jp_2950_;
}
}
else
{
lean_dec_ref(v___y_3000_);
if (lean_obj_tag(v___y_2996_) == 0)
{
uint8_t v___x_3014_; 
v___x_3014_ = 0;
v___y_2922_ = v___y_2997_;
v___y_2923_ = v___y_2998_;
v___y_2924_ = v___y_3003_;
v___y_2925_ = v___y_3008_;
v___y_2926_ = v___y_2999_;
v___y_2927_ = v___y_3002_;
v___y_2928_ = v_stxForExecution_3001_;
v___y_2929_ = v___y_3006_;
v___y_2930_ = v___y_3009_;
v___y_2931_ = v___y_2994_;
v___y_2932_ = v_a_3011_;
v___y_2933_ = v___y_3007_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v___y_3004_;
v___y_2936_ = v___y_3005_;
v___y_2937_ = v___x_3014_;
goto v___jp_2921_;
}
else
{
if (v___y_2999_ == 0)
{
v___y_2922_ = v___y_2997_;
v___y_2923_ = v___y_2998_;
v___y_2924_ = v___y_3003_;
v___y_2925_ = v___y_3008_;
v___y_2926_ = v___y_2999_;
v___y_2927_ = v___y_3002_;
v___y_2928_ = v_stxForExecution_3001_;
v___y_2929_ = v___y_3006_;
v___y_2930_ = v___y_3009_;
v___y_2931_ = v___y_2994_;
v___y_2932_ = v_a_3011_;
v___y_2933_ = v___y_3007_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v___y_3004_;
v___y_2936_ = v___y_3005_;
v___y_2937_ = v___y_2999_;
goto v___jp_2921_;
}
else
{
lean_object* v_ref_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_ref_3015_ = lean_ctor_get(v___y_3008_, 5);
v___x_3016_ = 0;
v___x_3017_ = l_Lean_SourceInfo_fromRef(v_ref_3015_, v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3019_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3018_);
v___x_3020_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_3021_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3024_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2994_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3026_; 
v_val_3025_ = lean_ctor_get(v___y_2994_, 0);
lean_inc(v_val_3025_);
lean_dec_ref(v___y_2994_);
v___x_3026_ = l_Array_mkArray1___redArg(v_val_3025_);
v___y_2893_ = v___y_2997_;
v___y_2894_ = v___y_2998_;
v___y_2895_ = v___x_3024_;
v___y_2896_ = v___y_3003_;
v___y_2897_ = v___x_3023_;
v___y_2898_ = v___y_3008_;
v___y_2899_ = v___y_2999_;
v___y_2900_ = v___y_3002_;
v___y_2901_ = v_stxForExecution_3001_;
v___y_2902_ = v___y_3006_;
v___y_2903_ = v___y_3009_;
v___y_2904_ = v___x_3019_;
v___y_2905_ = v_a_3011_;
v___y_2906_ = v___x_3022_;
v___y_2907_ = v___y_3007_;
v___y_2908_ = v___y_2996_;
v___y_2909_ = v___y_3004_;
v___y_2910_ = v___y_3005_;
v___y_2911_ = v___x_3017_;
v___y_2912_ = v___x_3026_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_3027_; 
lean_dec(v___y_2994_);
v___x_3027_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2893_ = v___y_2997_;
v___y_2894_ = v___y_2998_;
v___y_2895_ = v___x_3024_;
v___y_2896_ = v___y_3003_;
v___y_2897_ = v___x_3023_;
v___y_2898_ = v___y_3008_;
v___y_2899_ = v___y_2999_;
v___y_2900_ = v___y_3002_;
v___y_2901_ = v_stxForExecution_3001_;
v___y_2902_ = v___y_3006_;
v___y_2903_ = v___y_3009_;
v___y_2904_ = v___x_3019_;
v___y_2905_ = v_a_3011_;
v___y_2906_ = v___x_3022_;
v___y_2907_ = v___y_3007_;
v___y_2908_ = v___y_2996_;
v___y_2909_ = v___y_3004_;
v___y_2910_ = v___y_3005_;
v___y_2911_ = v___x_3017_;
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
lean_inc_ref(v___y_3045_);
v___x_3051_ = l_Array_append___redArg(v___y_3045_, v___y_3050_);
lean_dec_ref(v___y_3050_);
lean_inc(v___y_3046_);
lean_inc(v___y_3034_);
v___x_3052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3034_);
lean_ctor_set(v___x_3052_, 1, v___y_3046_);
lean_ctor_set(v___x_3052_, 2, v___x_3051_);
lean_inc(v___y_3034_);
v___x_3053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3034_);
lean_ctor_set(v___x_3053_, 1, v___y_3046_);
lean_ctor_set(v___x_3053_, 2, v___y_3045_);
lean_inc(v___y_3030_);
v___x_3054_ = l_Lean_Syntax_node5(v___y_3034_, v___y_3047_, v___y_3033_, v___y_3030_, v___y_3049_, v___x_3052_, v___x_3053_);
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3031_;
v___y_2999_ = v___y_3036_;
v___y_3000_ = v___y_3038_;
v_stxForExecution_3001_ = v___x_3054_;
v___y_3002_ = v___y_3048_;
v___y_3003_ = v___y_3043_;
v___y_3004_ = v___y_3039_;
v___y_3005_ = v___y_3037_;
v___y_3006_ = v___y_3041_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3040_;
v___y_3009_ = v___y_3035_;
goto v___jp_2993_;
}
v___jp_3055_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_inc_ref(v___y_3072_);
v___x_3077_ = l_Array_append___redArg(v___y_3072_, v___y_3076_);
lean_dec_ref(v___y_3076_);
lean_inc(v___y_3074_);
lean_inc(v___y_3061_);
v___x_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___y_3061_);
lean_ctor_set(v___x_3078_, 1, v___y_3074_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
if (lean_obj_tag(v___y_3059_) == 1)
{
lean_object* v_val_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_val_3079_ = lean_ctor_get(v___y_3059_, 0);
v___x_3080_ = l_Lean_SourceInfo_fromRef(v_val_3079_, v___x_2524_);
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
v___y_3040_ = v___y_3068_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3072_;
v___y_3046_ = v___y_3074_;
v___y_3047_ = v___y_3073_;
v___y_3048_ = v___y_3075_;
v___y_3049_ = v___x_3078_;
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
v___y_3040_ = v___y_3068_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3072_;
v___y_3046_ = v___y_3074_;
v___y_3047_ = v___y_3073_;
v___y_3048_ = v___y_3075_;
v___y_3049_ = v___x_3078_;
v___y_3050_ = v___x_3084_;
goto v___jp_3028_;
}
}
v___jp_3085_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_inc_ref(v___y_3104_);
v___x_3108_ = l_Array_append___redArg(v___y_3104_, v___y_3107_);
lean_dec_ref(v___y_3107_);
lean_inc(v___y_3102_);
lean_inc(v___y_3088_);
v___x_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3088_);
lean_ctor_set(v___x_3109_, 1, v___y_3102_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_3088_);
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3088_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3113_ = l_Lean_Syntax_SepArray_ofElems(v___x_3112_, v___y_3095_);
v___x_3114_ = l_Array_append___redArg(v___y_3104_, v___x_3113_);
lean_dec_ref(v___x_3113_);
lean_inc(v___y_3102_);
lean_inc(v___y_3088_);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___y_3088_);
lean_ctor_set(v___x_3115_, 1, v___y_3102_);
lean_ctor_set(v___x_3115_, 2, v___x_3114_);
v___x_3116_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_3088_);
v___x_3117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___y_3088_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
lean_inc(v___y_3088_);
v___x_3118_ = l_Lean_Syntax_node3(v___y_3088_, v___y_3102_, v___x_3111_, v___x_3115_, v___x_3117_);
lean_inc(v___y_3087_);
v___x_3119_ = l_Lean_Syntax_node5(v___y_3088_, v___y_3105_, v___y_3096_, v___y_3087_, v___y_3093_, v___x_3109_, v___x_3118_);
v___y_2994_ = v___y_3100_;
v___y_2995_ = v___y_3087_;
v___y_2996_ = v___y_3103_;
v___y_2997_ = v___y_3090_;
v___y_2998_ = v___y_3089_;
v___y_2999_ = v___y_3092_;
v___y_3000_ = v___y_3095_;
v_stxForExecution_3001_ = v___x_3119_;
v___y_3002_ = v___y_3106_;
v___y_3003_ = v___y_3101_;
v___y_3004_ = v___y_3097_;
v___y_3005_ = v___y_3094_;
v___y_3006_ = v___y_3099_;
v___y_3007_ = v___y_3086_;
v___y_3008_ = v___y_3098_;
v___y_3009_ = v___y_3091_;
goto v___jp_2993_;
}
v___jp_3120_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_inc_ref(v___y_3139_);
v___x_3142_ = l_Array_append___redArg(v___y_3139_, v___y_3141_);
lean_dec_ref(v___y_3141_);
lean_inc(v___y_3136_);
lean_inc(v___y_3123_);
v___x_3143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3143_, 0, v___y_3123_);
lean_ctor_set(v___x_3143_, 1, v___y_3136_);
lean_ctor_set(v___x_3143_, 2, v___x_3142_);
if (lean_obj_tag(v___y_3125_) == 1)
{
lean_object* v_val_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_val_3144_ = lean_ctor_get(v___y_3125_, 0);
v___x_3145_ = l_Lean_SourceInfo_fromRef(v_val_3144_, v___x_2524_);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Array_mkArray1___redArg(v___x_3147_);
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___y_3123_;
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___y_3125_;
v___y_3091_ = v___y_3126_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___x_3143_;
v___y_3094_ = v___y_3128_;
v___y_3095_ = v___y_3129_;
v___y_3096_ = v___y_3130_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3132_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3136_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___y_3139_;
v___y_3105_ = v___y_3137_;
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
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___y_3125_;
v___y_3091_ = v___y_3126_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___x_3143_;
v___y_3094_ = v___y_3128_;
v___y_3095_ = v___y_3129_;
v___y_3096_ = v___y_3130_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3132_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3136_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___y_3139_;
v___y_3105_ = v___y_3137_;
v___y_3106_ = v___y_3140_;
v___y_3107_ = v___x_3149_;
goto v___jp_3085_;
}
}
v___jp_3150_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_inc_ref(v___y_3169_);
v___x_3173_ = l_Array_append___redArg(v___y_3169_, v___y_3172_);
lean_dec_ref(v___y_3172_);
lean_inc(v___y_3171_);
lean_inc(v___y_3168_);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3168_);
lean_ctor_set(v___x_3174_, 1, v___y_3171_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_3168_);
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3168_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3178_ = l_Lean_Syntax_SepArray_ofElems(v___x_3177_, v___y_3160_);
v___x_3179_ = l_Array_append___redArg(v___y_3169_, v___x_3178_);
lean_dec_ref(v___x_3178_);
lean_inc(v___y_3171_);
lean_inc(v___y_3168_);
v___x_3180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3180_, 0, v___y_3168_);
lean_ctor_set(v___x_3180_, 1, v___y_3171_);
lean_ctor_set(v___x_3180_, 2, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_3168_);
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___y_3168_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
lean_inc(v___y_3168_);
v___x_3183_ = l_Lean_Syntax_node3(v___y_3168_, v___y_3171_, v___x_3176_, v___x_3180_, v___x_3182_);
lean_inc(v___y_3152_);
v___x_3184_ = l_Lean_Syntax_node5(v___y_3168_, v___y_3157_, v___y_3167_, v___y_3152_, v___y_3158_, v___x_3174_, v___x_3183_);
v___y_2994_ = v___y_3164_;
v___y_2995_ = v___y_3152_;
v___y_2996_ = v___y_3166_;
v___y_2997_ = v___y_3154_;
v___y_2998_ = v___y_3153_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3160_;
v_stxForExecution_3001_ = v___x_3184_;
v___y_3002_ = v___y_3170_;
v___y_3003_ = v___y_3165_;
v___y_3004_ = v___y_3161_;
v___y_3005_ = v___y_3159_;
v___y_3006_ = v___y_3163_;
v___y_3007_ = v___y_3151_;
v___y_3008_ = v___y_3162_;
v___y_3009_ = v___y_3155_;
goto v___jp_2993_;
}
v___jp_3185_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc_ref(v___y_3203_);
v___x_3207_ = l_Array_append___redArg(v___y_3203_, v___y_3206_);
lean_dec_ref(v___y_3206_);
lean_inc(v___y_3205_);
lean_inc(v___y_3202_);
v___x_3208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3208_, 0, v___y_3202_);
lean_ctor_set(v___x_3208_, 1, v___y_3205_);
lean_ctor_set(v___x_3208_, 2, v___x_3207_);
if (lean_obj_tag(v___y_3189_) == 1)
{
lean_object* v_val_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_val_3209_ = lean_ctor_get(v___y_3189_, 0);
v___x_3210_ = l_Lean_SourceInfo_fromRef(v_val_3209_, v___x_2524_);
v___x_3211_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Array_mkArray1___redArg(v___x_3212_);
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___x_3208_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___y_3197_;
v___y_3163_ = v___y_3196_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___y_3199_;
v___y_3166_ = v___y_3201_;
v___y_3167_ = v___y_3200_;
v___y_3168_ = v___y_3202_;
v___y_3169_ = v___y_3203_;
v___y_3170_ = v___y_3204_;
v___y_3171_ = v___y_3205_;
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
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___x_3208_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___y_3197_;
v___y_3163_ = v___y_3196_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___y_3199_;
v___y_3166_ = v___y_3201_;
v___y_3167_ = v___y_3200_;
v___y_3168_ = v___y_3202_;
v___y_3169_ = v___y_3203_;
v___y_3170_ = v___y_3204_;
v___y_3171_ = v___y_3205_;
v___y_3172_ = v___x_3214_;
goto v___jp_3150_;
}
}
v___jp_3215_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc_ref(v___y_3225_);
v___x_3238_ = l_Array_append___redArg(v___y_3225_, v___y_3237_);
lean_dec_ref(v___y_3237_);
lean_inc(v___y_3234_);
lean_inc(v___y_3230_);
v___x_3239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3239_, 0, v___y_3230_);
lean_ctor_set(v___x_3239_, 1, v___y_3234_);
lean_ctor_set(v___x_3239_, 2, v___x_3238_);
lean_inc(v___y_3230_);
v___x_3240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___y_3230_);
lean_ctor_set(v___x_3240_, 1, v___y_3234_);
lean_ctor_set(v___x_3240_, 2, v___y_3225_);
lean_inc(v___y_3217_);
v___x_3241_ = l_Lean_Syntax_node5(v___y_3230_, v___y_3233_, v___y_3224_, v___y_3217_, v___y_3235_, v___x_3239_, v___x_3240_);
v___y_2994_ = v___y_3229_;
v___y_2995_ = v___y_3217_;
v___y_2996_ = v___y_3232_;
v___y_2997_ = v___y_3219_;
v___y_2998_ = v___y_3218_;
v___y_2999_ = v___y_3221_;
v___y_3000_ = v___y_3223_;
v_stxForExecution_3001_ = v___x_3241_;
v___y_3002_ = v___y_3236_;
v___y_3003_ = v___y_3231_;
v___y_3004_ = v___y_3226_;
v___y_3005_ = v___y_3222_;
v___y_3006_ = v___y_3228_;
v___y_3007_ = v___y_3216_;
v___y_3008_ = v___y_3227_;
v___y_3009_ = v___y_3220_;
goto v___jp_2993_;
}
v___jp_3242_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_inc_ref(v___y_3252_);
v___x_3264_ = l_Array_append___redArg(v___y_3252_, v___y_3263_);
lean_dec_ref(v___y_3263_);
lean_inc(v___y_3261_);
lean_inc(v___y_3258_);
v___x_3265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3265_, 0, v___y_3258_);
lean_ctor_set(v___x_3265_, 1, v___y_3261_);
lean_ctor_set(v___x_3265_, 2, v___x_3264_);
if (lean_obj_tag(v___y_3246_) == 1)
{
lean_object* v_val_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_val_3266_ = lean_ctor_get(v___y_3246_, 0);
v___x_3267_ = l_Lean_SourceInfo_fromRef(v_val_3266_, v___x_2524_);
v___x_3268_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = l_Array_mkArray1___redArg(v___x_3269_);
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3246_;
v___y_3220_ = v___y_3247_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3250_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3255_;
v___y_3228_ = v___y_3254_;
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
v___y_3220_ = v___y_3247_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3250_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3255_;
v___y_3228_ = v___y_3254_;
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
v_ref_3289_ = lean_ctor_get(v___y_3282_, 5);
v___x_3290_ = l_Lean_SourceInfo_fromRef(v_ref_3289_, v___y_3288_);
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3292_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3291_);
v___x_3293_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_3294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3297_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3284_) == 1)
{
lean_object* v_val_3298_; lean_object* v___x_3299_; 
v_val_3298_ = lean_ctor_get(v___y_3284_, 0);
lean_inc(v_val_3298_);
v___x_3299_ = l_Array_mkArray1___redArg(v_val_3298_);
v___y_3056_ = v___y_3273_;
v___y_3057_ = v___y_3274_;
v___y_3058_ = v___y_3275_;
v___y_3059_ = v___y_3276_;
v___y_3060_ = v___x_3295_;
v___y_3061_ = v___x_3290_;
v___y_3062_ = v___y_3277_;
v___y_3063_ = v___y_3278_;
v___y_3064_ = v___y_3279_;
v___y_3065_ = v___y_3280_;
v___y_3066_ = v___y_3281_;
v___y_3067_ = v___y_3283_;
v___y_3068_ = v___y_3282_;
v___y_3069_ = v___y_3284_;
v___y_3070_ = v___y_3285_;
v___y_3071_ = v___y_3286_;
v___y_3072_ = v___x_3297_;
v___y_3073_ = v___x_3292_;
v___y_3074_ = v___x_3296_;
v___y_3075_ = v___y_3287_;
v___y_3076_ = v___x_3299_;
goto v___jp_3055_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3056_ = v___y_3273_;
v___y_3057_ = v___y_3274_;
v___y_3058_ = v___y_3275_;
v___y_3059_ = v___y_3276_;
v___y_3060_ = v___x_3295_;
v___y_3061_ = v___x_3290_;
v___y_3062_ = v___y_3277_;
v___y_3063_ = v___y_3278_;
v___y_3064_ = v___y_3279_;
v___y_3065_ = v___y_3280_;
v___y_3066_ = v___y_3281_;
v___y_3067_ = v___y_3283_;
v___y_3068_ = v___y_3282_;
v___y_3069_ = v___y_3284_;
v___y_3070_ = v___y_3285_;
v___y_3071_ = v___y_3286_;
v___y_3072_ = v___x_3297_;
v___y_3073_ = v___x_3292_;
v___y_3074_ = v___x_3296_;
v___y_3075_ = v___y_3287_;
v___y_3076_ = v___x_3300_;
goto v___jp_3055_;
}
}
v___jp_3301_:
{
if (v___y_3318_ == 0)
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_ref_3319_ = lean_ctor_get(v___y_3311_, 5);
v___x_3320_ = l_Lean_SourceInfo_fromRef(v_ref_3319_, v___y_3318_);
v___x_3321_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3322_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3321_);
v___x_3323_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3327_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3313_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3328_);
v___x_3329_ = l_Array_mkArray1___redArg(v_val_3328_);
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3303_;
v___y_3123_ = v___x_3320_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___y_3305_;
v___y_3126_ = v___y_3306_;
v___y_3127_ = v___y_3307_;
v___y_3128_ = v___y_3308_;
v___y_3129_ = v___y_3309_;
v___y_3130_ = v___x_3325_;
v___y_3131_ = v___y_3310_;
v___y_3132_ = v___y_3312_;
v___y_3133_ = v___y_3311_;
v___y_3134_ = v___y_3313_;
v___y_3135_ = v___y_3314_;
v___y_3136_ = v___x_3326_;
v___y_3137_ = v___x_3322_;
v___y_3138_ = v___y_3315_;
v___y_3139_ = v___x_3327_;
v___y_3140_ = v___y_3316_;
v___y_3141_ = v___x_3329_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3303_;
v___y_3123_ = v___x_3320_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___y_3305_;
v___y_3126_ = v___y_3306_;
v___y_3127_ = v___y_3307_;
v___y_3128_ = v___y_3308_;
v___y_3129_ = v___y_3309_;
v___y_3130_ = v___x_3325_;
v___y_3131_ = v___y_3310_;
v___y_3132_ = v___y_3312_;
v___y_3133_ = v___y_3311_;
v___y_3134_ = v___y_3313_;
v___y_3135_ = v___y_3314_;
v___y_3136_ = v___x_3326_;
v___y_3137_ = v___x_3322_;
v___y_3138_ = v___y_3315_;
v___y_3139_ = v___x_3327_;
v___y_3140_ = v___y_3316_;
v___y_3141_ = v___x_3330_;
goto v___jp_3120_;
}
}
else
{
lean_object* v_ref_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_ref_3331_ = lean_ctor_get(v___y_3311_, 5);
v___x_3332_ = l_Lean_SourceInfo_fromRef(v_ref_3331_, v___y_3317_);
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3334_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3333_);
v___x_3335_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3339_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3313_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3341_; 
v_val_3340_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3340_);
v___x_3341_ = l_Array_mkArray1___redArg(v_val_3340_);
v___y_3186_ = v___y_3302_;
v___y_3187_ = v___y_3303_;
v___y_3188_ = v___y_3304_;
v___y_3189_ = v___y_3305_;
v___y_3190_ = v___y_3306_;
v___y_3191_ = v___y_3307_;
v___y_3192_ = v___x_3334_;
v___y_3193_ = v___y_3308_;
v___y_3194_ = v___y_3309_;
v___y_3195_ = v___y_3310_;
v___y_3196_ = v___y_3312_;
v___y_3197_ = v___y_3311_;
v___y_3198_ = v___y_3313_;
v___y_3199_ = v___y_3314_;
v___y_3200_ = v___x_3337_;
v___y_3201_ = v___y_3315_;
v___y_3202_ = v___x_3332_;
v___y_3203_ = v___x_3339_;
v___y_3204_ = v___y_3316_;
v___y_3205_ = v___x_3338_;
v___y_3206_ = v___x_3341_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3186_ = v___y_3302_;
v___y_3187_ = v___y_3303_;
v___y_3188_ = v___y_3304_;
v___y_3189_ = v___y_3305_;
v___y_3190_ = v___y_3306_;
v___y_3191_ = v___y_3307_;
v___y_3192_ = v___x_3334_;
v___y_3193_ = v___y_3308_;
v___y_3194_ = v___y_3309_;
v___y_3195_ = v___y_3310_;
v___y_3196_ = v___y_3312_;
v___y_3197_ = v___y_3311_;
v___y_3198_ = v___y_3313_;
v___y_3199_ = v___y_3314_;
v___y_3200_ = v___x_3337_;
v___y_3201_ = v___y_3315_;
v___y_3202_ = v___x_3332_;
v___y_3203_ = v___x_3339_;
v___y_3204_ = v___y_3316_;
v___y_3205_ = v___x_3338_;
v___y_3206_ = v___x_3342_;
goto v___jp_3185_;
}
}
}
v___jp_3343_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = lean_array_get_size(v_argsArray_3350_);
v___x_3360_ = lean_nat_dec_eq(v___x_3359_, v___x_2539_);
if (v___x_3360_ == 0)
{
if (lean_obj_tag(v___y_3346_) == 0)
{
v___y_3302_ = v___y_3356_;
v___y_3303_ = v___y_3345_;
v___y_3304_ = v___y_3347_;
v___y_3305_ = v___y_3348_;
v___y_3306_ = v___y_3358_;
v___y_3307_ = v___y_3349_;
v___y_3308_ = v___y_3354_;
v___y_3309_ = v_argsArray_3350_;
v___y_3310_ = v___y_3353_;
v___y_3311_ = v___y_3357_;
v___y_3312_ = v___y_3355_;
v___y_3313_ = v___y_3344_;
v___y_3314_ = v___y_3352_;
v___y_3315_ = v___y_3346_;
v___y_3316_ = v___y_3351_;
v___y_3317_ = v___x_3360_;
v___y_3318_ = v___x_3360_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___y_3356_;
v___y_3303_ = v___y_3345_;
v___y_3304_ = v___y_3347_;
v___y_3305_ = v___y_3348_;
v___y_3306_ = v___y_3358_;
v___y_3307_ = v___y_3349_;
v___y_3308_ = v___y_3354_;
v___y_3309_ = v_argsArray_3350_;
v___y_3310_ = v___y_3353_;
v___y_3311_ = v___y_3357_;
v___y_3312_ = v___y_3355_;
v___y_3313_ = v___y_3344_;
v___y_3314_ = v___y_3352_;
v___y_3315_ = v___y_3346_;
v___y_3316_ = v___y_3351_;
v___y_3317_ = v___x_3360_;
v___y_3318_ = v___y_3349_;
goto v___jp_3301_;
}
}
else
{
if (lean_obj_tag(v___y_3346_) == 0)
{
uint8_t v___x_3361_; 
v___x_3361_ = 0;
v___y_3273_ = v___y_3356_;
v___y_3274_ = v___y_3345_;
v___y_3275_ = v___y_3347_;
v___y_3276_ = v___y_3348_;
v___y_3277_ = v___y_3358_;
v___y_3278_ = v___y_3349_;
v___y_3279_ = v___y_3354_;
v___y_3280_ = v_argsArray_3350_;
v___y_3281_ = v___y_3353_;
v___y_3282_ = v___y_3357_;
v___y_3283_ = v___y_3355_;
v___y_3284_ = v___y_3344_;
v___y_3285_ = v___y_3352_;
v___y_3286_ = v___y_3346_;
v___y_3287_ = v___y_3351_;
v___y_3288_ = v___x_3361_;
goto v___jp_3272_;
}
else
{
if (v___y_3349_ == 0)
{
v___y_3273_ = v___y_3356_;
v___y_3274_ = v___y_3345_;
v___y_3275_ = v___y_3347_;
v___y_3276_ = v___y_3348_;
v___y_3277_ = v___y_3358_;
v___y_3278_ = v___y_3349_;
v___y_3279_ = v___y_3354_;
v___y_3280_ = v_argsArray_3350_;
v___y_3281_ = v___y_3353_;
v___y_3282_ = v___y_3357_;
v___y_3283_ = v___y_3355_;
v___y_3284_ = v___y_3344_;
v___y_3285_ = v___y_3352_;
v___y_3286_ = v___y_3346_;
v___y_3287_ = v___y_3351_;
v___y_3288_ = v___y_3349_;
goto v___jp_3272_;
}
else
{
lean_object* v_ref_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_ref_3362_ = lean_ctor_get(v___y_3357_, 5);
v___x_3363_ = 0;
v___x_3364_ = l_Lean_SourceInfo_fromRef(v_ref_3362_, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3366_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3365_);
v___x_3367_ = l_Lean_SourceInfo_fromRef(v_tk_2540_, v___x_2524_);
v___x_3368_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3371_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3344_) == 1)
{
lean_object* v_val_3372_; lean_object* v___x_3373_; 
v_val_3372_ = lean_ctor_get(v___y_3344_, 0);
lean_inc(v_val_3372_);
v___x_3373_ = l_Array_mkArray1___redArg(v_val_3372_);
v___y_3243_ = v___y_3356_;
v___y_3244_ = v___y_3345_;
v___y_3245_ = v___y_3347_;
v___y_3246_ = v___y_3348_;
v___y_3247_ = v___y_3358_;
v___y_3248_ = v___y_3349_;
v___y_3249_ = v___y_3354_;
v___y_3250_ = v_argsArray_3350_;
v___y_3251_ = v___x_3369_;
v___y_3252_ = v___x_3371_;
v___y_3253_ = v___y_3353_;
v___y_3254_ = v___y_3355_;
v___y_3255_ = v___y_3357_;
v___y_3256_ = v___y_3344_;
v___y_3257_ = v___y_3352_;
v___y_3258_ = v___x_3364_;
v___y_3259_ = v___y_3346_;
v___y_3260_ = v___x_3366_;
v___y_3261_ = v___x_3370_;
v___y_3262_ = v___y_3351_;
v___y_3263_ = v___x_3373_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3243_ = v___y_3356_;
v___y_3244_ = v___y_3345_;
v___y_3245_ = v___y_3347_;
v___y_3246_ = v___y_3348_;
v___y_3247_ = v___y_3358_;
v___y_3248_ = v___y_3349_;
v___y_3249_ = v___y_3354_;
v___y_3250_ = v_argsArray_3350_;
v___y_3251_ = v___x_3369_;
v___y_3252_ = v___x_3371_;
v___y_3253_ = v___y_3353_;
v___y_3254_ = v___y_3355_;
v___y_3255_ = v___y_3357_;
v___y_3256_ = v___y_3344_;
v___y_3257_ = v___y_3352_;
v___y_3258_ = v___x_3364_;
v___y_3259_ = v___y_3346_;
v___y_3260_ = v___x_3366_;
v___y_3261_ = v___x_3370_;
v___y_3262_ = v___y_3351_;
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
v___x_3392_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3387_, v___y_3376_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3392_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3376_);
v___x_3394_ = l_Lean_LibrarySuggestions_select(v_a_3393_, v___y_3391_, v___y_3376_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; size_t v_sz_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v_sz_3396_ = lean_array_size(v_a_3395_);
v___x_3397_ = ((size_t)0ULL);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3376_);
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3388_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3395_, v_sz_3396_, v___x_3397_, v___y_3390_, v___y_3388_, v___y_3387_, v___y_3380_, v___y_3381_, v___y_3376_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v_a_3395_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___y_3344_ = v___y_3386_;
v___y_3345_ = v___y_3377_;
v___y_3346_ = v___y_3389_;
v___y_3347_ = v___y_3379_;
v___y_3348_ = v___y_3378_;
v___y_3349_ = v___y_3382_;
v_argsArray_3350_ = v_a_3399_;
v___y_3351_ = v___y_3388_;
v___y_3352_ = v___y_3387_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3381_;
v___y_3355_ = v___y_3376_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3384_;
v___y_3358_ = v___y_3385_;
goto v___jp_3343_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
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
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
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
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
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
uint8_t v_suggestions_3441_; 
v_suggestions_3441_ = lean_ctor_get_uint8(v___y_3439_, sizeof(void*)*3 + 26);
if (v_suggestions_3441_ == 0)
{
lean_dec_ref(v___y_3439_);
lean_dec_ref(v___f_2528_);
v___y_3344_ = v___y_3435_;
v___y_3345_ = v___y_3426_;
v___y_3346_ = v___y_3437_;
v___y_3347_ = v___y_3428_;
v___y_3348_ = v___y_3427_;
v___y_3349_ = v___y_3431_;
v_argsArray_3350_ = v___y_3440_;
v___y_3351_ = v___y_3438_;
v___y_3352_ = v___y_3436_;
v___y_3353_ = v___y_3429_;
v___y_3354_ = v___y_3430_;
v___y_3355_ = v___y_3425_;
v___y_3356_ = v___y_3432_;
v___y_3357_ = v___y_3433_;
v___y_3358_ = v___y_3434_;
goto v___jp_3343_;
}
else
{
lean_object* v_maxSuggestions_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_maxSuggestions_3442_ = lean_ctor_get(v___y_3439_, 2);
lean_inc(v_maxSuggestions_3442_);
lean_dec_ref(v___y_3439_);
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3444_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3442_) == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_unsigned_to_nat(100u);
v___x_3446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v___x_3443_);
lean_ctor_set(v___x_3446_, 2, v___f_2528_);
lean_ctor_set(v___x_3446_, 3, v___x_3444_);
v___y_3376_ = v___y_3425_;
v___y_3377_ = v___y_3426_;
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
v___y_3388_ = v___y_3438_;
v___y_3389_ = v___y_3437_;
v___y_3390_ = v___y_3440_;
v___y_3391_ = v___x_3446_;
goto v___jp_3375_;
}
else
{
lean_object* v_val_3447_; lean_object* v___x_3448_; 
v_val_3447_ = lean_ctor_get(v_maxSuggestions_3442_, 0);
lean_inc(v_val_3447_);
lean_dec_ref(v_maxSuggestions_3442_);
v___x_3448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3448_, 0, v_val_3447_);
lean_ctor_set(v___x_3448_, 1, v___x_3443_);
lean_ctor_set(v___x_3448_, 2, v___f_2528_);
lean_ctor_set(v___x_3448_, 3, v___x_3444_);
v___y_3376_ = v___y_3425_;
v___y_3377_ = v___y_3426_;
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
v___y_3388_ = v___y_3438_;
v___y_3389_ = v___y_3437_;
v___y_3390_ = v___y_3440_;
v___y_3391_ = v___x_3448_;
goto v___jp_3375_;
}
}
}
v___jp_3449_:
{
uint8_t v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = 1;
lean_inc(v___y_3459_);
lean_inc_ref(v___y_3458_);
lean_inc(v___y_3457_);
lean_inc_ref(v___y_3450_);
lean_inc(v___y_3455_);
lean_inc_ref(v___y_3454_);
lean_inc(v___y_3451_);
v___x_3465_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3451_, v___x_3464_, v___y_3462_, v___y_3454_, v___y_3455_, v___y_3450_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3465_) == 0)
{
if (lean_obj_tag(v___y_3452_) == 1)
{
lean_object* v_a_3466_; lean_object* v_val_3467_; lean_object* v___x_3468_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref(v___x_3465_);
v_val_3467_ = lean_ctor_get(v___y_3452_, 0);
lean_inc(v_val_3467_);
lean_dec_ref(v___y_3452_);
v___x_3468_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3467_);
lean_dec(v_val_3467_);
v___y_3425_ = v___y_3450_;
v___y_3426_ = v___y_3451_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___x_3464_;
v___y_3429_ = v___y_3454_;
v___y_3430_ = v___y_3455_;
v___y_3431_ = v___y_3456_;
v___y_3432_ = v___y_3457_;
v___y_3433_ = v___y_3458_;
v___y_3434_ = v___y_3459_;
v___y_3435_ = v___y_3463_;
v___y_3436_ = v___y_3460_;
v___y_3437_ = v___y_3461_;
v___y_3438_ = v___y_3462_;
v___y_3439_ = v_a_3466_;
v___y_3440_ = v___x_3468_;
goto v___jp_3424_;
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3470_; 
lean_dec(v___y_3452_);
v_a_3469_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3469_);
lean_dec_ref(v___x_3465_);
v___x_3470_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3425_ = v___y_3450_;
v___y_3426_ = v___y_3451_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___x_3464_;
v___y_3429_ = v___y_3454_;
v___y_3430_ = v___y_3455_;
v___y_3431_ = v___y_3456_;
v___y_3432_ = v___y_3457_;
v___y_3433_ = v___y_3458_;
v___y_3434_ = v___y_3459_;
v___y_3435_ = v___y_3463_;
v___y_3436_ = v___y_3460_;
v___y_3437_ = v___y_3461_;
v___y_3438_ = v___y_3462_;
v___y_3439_ = v_a_3469_;
v___y_3440_ = v___x_3470_;
goto v___jp_3424_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v_a_3471_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3465_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3465_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
v___jp_3479_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Syntax_getOptional_x3f(v___y_3483_);
lean_dec(v___y_3483_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_box(0);
v___y_3450_ = v___y_3490_;
v___y_3451_ = v___y_3480_;
v___y_3452_ = v_args_3485_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3488_;
v___y_3455_ = v___y_3489_;
v___y_3456_ = v___y_3484_;
v___y_3457_ = v___y_3491_;
v___y_3458_ = v___y_3492_;
v___y_3459_ = v___y_3493_;
v___y_3460_ = v___y_3487_;
v___y_3461_ = v___y_3481_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___x_3495_;
goto v___jp_3449_;
}
else
{
lean_object* v_val_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
v_val_3496_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3494_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_val_3496_);
lean_dec(v___x_3494_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_val_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
v___y_3450_ = v___y_3490_;
v___y_3451_ = v___y_3480_;
v___y_3452_ = v_args_3485_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3488_;
v___y_3455_ = v___y_3489_;
v___y_3456_ = v___y_3484_;
v___y_3457_ = v___y_3491_;
v___y_3458_ = v___y_3492_;
v___y_3459_ = v___y_3493_;
v___y_3460_ = v___y_3487_;
v___y_3461_ = v___y_3481_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___x_3501_;
goto v___jp_3449_;
}
}
}
}
v___jp_3505_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = lean_unsigned_to_nat(3u);
v___x_3521_ = l_Lean_Syntax_getArg(v___y_3510_, v___x_3520_);
lean_dec(v___y_3510_);
v___x_3522_ = l_Lean_Syntax_isNone(v___x_3521_);
if (v___x_3522_ == 0)
{
uint8_t v___x_3523_; 
lean_inc(v___x_3521_);
v___x_3523_ = l_Lean_Syntax_matchesNull(v___x_3521_, v___x_3504_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v___x_3521_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v_o_3511_);
lean_dec(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3525_ = l_Lean_Syntax_getArg(v___x_3521_, v___x_2539_);
lean_dec(v___x_3521_);
v___x_3526_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3527_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3526_);
lean_inc(v___x_3525_);
v___x_3528_ = l_Lean_Syntax_isOfKind(v___x_3525_, v___x_3527_);
lean_dec(v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
lean_dec(v___x_3525_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v_o_3511_);
lean_dec(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3529_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v_args_3531_; lean_object* v___x_3532_; 
v___x_3530_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3504_);
lean_dec(v___x_3525_);
v_args_3531_ = l_Lean_Syntax_getArgs(v___x_3530_);
lean_dec(v___x_3530_);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_args_3531_);
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v_o_3511_;
v___y_3483_ = v___y_3508_;
v___y_3484_ = v___y_3509_;
v_args_3485_ = v___x_3532_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
goto v___jp_3479_;
}
}
}
else
{
lean_object* v___x_3533_; 
lean_dec(v___x_3521_);
v___x_3533_ = lean_box(0);
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v_o_3511_;
v___y_3483_ = v___y_3508_;
v___y_3484_ = v___y_3509_;
v_args_3485_ = v___x_3533_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
goto v___jp_3479_;
}
}
v___jp_3534_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3544_ = lean_unsigned_to_nat(2u);
v___x_3545_ = l_Lean_Syntax_getArg(v_stx_2523_, v___x_3544_);
v___x_3546_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3547_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3546_);
lean_inc(v___x_3545_);
v___x_3548_ = l_Lean_Syntax_isOfKind(v___x_3545_, v___x_3547_);
lean_dec(v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v___x_3545_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v_bang_3535_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3549_;
}
else
{
lean_object* v_cfg_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v_cfg_3550_ = l_Lean_Syntax_getArg(v___x_3545_, v___x_2539_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2527_);
lean_inc_ref(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_3552_ = l_Lean_Name_mkStr4(v___x_2525_, v___x_2526_, v___x_2527_, v___x_3551_);
lean_inc(v_cfg_3550_);
v___x_3553_ = l_Lean_Syntax_isOfKind(v_cfg_3550_, v___x_3552_);
lean_dec(v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_dec(v_cfg_3550_);
lean_dec(v___x_3545_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v_bang_3535_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v___x_3555_ = l_Lean_Syntax_getArg(v___x_3545_, v___x_3504_);
v___x_3556_ = l_Lean_Syntax_getArg(v___x_3545_, v___x_3544_);
v___x_3557_ = l_Lean_Syntax_isNone(v___x_3556_);
if (v___x_3557_ == 0)
{
uint8_t v___x_3558_; 
lean_inc(v___x_3556_);
v___x_3558_ = l_Lean_Syntax_matchesNull(v___x_3556_, v___x_3504_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_dec(v___x_3556_);
lean_dec(v___x_3555_);
lean_dec(v_cfg_3550_);
lean_dec(v___x_3545_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v_bang_3535_);
lean_dec(v_tk_2540_);
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___x_2525_);
v___x_3559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3559_;
}
else
{
lean_object* v_o_3560_; lean_object* v___x_3561_; 
v_o_3560_ = l_Lean_Syntax_getArg(v___x_3556_, v___x_2539_);
lean_dec(v___x_3556_);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_o_3560_);
v___y_3506_ = v_cfg_3550_;
v___y_3507_ = v_bang_3535_;
v___y_3508_ = v___x_3555_;
v___y_3509_ = v___x_3553_;
v___y_3510_ = v___x_3545_;
v_o_3511_ = v___x_3561_;
v___y_3512_ = v___y_3536_;
v___y_3513_ = v___y_3537_;
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___y_3539_;
v___y_3516_ = v___y_3540_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3542_;
v___y_3519_ = v___y_3543_;
goto v___jp_3505_;
}
}
else
{
lean_object* v___x_3562_; 
lean_dec(v___x_3556_);
v___x_3562_ = lean_box(0);
v___y_3506_ = v_cfg_3550_;
v___y_3507_ = v_bang_3535_;
v___y_3508_ = v___x_3555_;
v___y_3509_ = v___x_3553_;
v___y_3510_ = v___x_3545_;
v_o_3511_ = v___x_3562_;
v___y_3512_ = v___y_3536_;
v___y_3513_ = v___y_3537_;
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___y_3539_;
v___y_3516_ = v___y_3540_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3542_;
v___y_3519_ = v___y_3543_;
goto v___jp_3505_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3570_, lean_object* v_stx_3571_, lean_object* v___x_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v___x_3575_, lean_object* v___f_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
uint8_t v___x_39413__boxed_3586_; uint8_t v___x_39414__boxed_3587_; lean_object* v_res_3588_; 
v___x_39413__boxed_3586_ = lean_unbox(v___x_3570_);
v___x_39414__boxed_3587_ = lean_unbox(v___x_3572_);
v_res_3588_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39413__boxed_3586_, v_stx_3571_, v___x_39414__boxed_3587_, v___x_3573_, v___x_3574_, v___x_3575_, v___f_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v_stx_3571_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; uint8_t v___x_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___y_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3595_);
v___x_3609_ = l_Lean_Syntax_isOfKind(v_stx_3595_, v___x_3608_);
v___x_3610_ = 1;
v___f_3611_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3612_ = lean_box(v___x_3609_);
v___x_3613_ = lean_box(v___x_3610_);
v___y_3614_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3614_, 0, v___x_3612_);
lean_closure_set(v___y_3614_, 1, v_stx_3595_);
lean_closure_set(v___y_3614_, 2, v___x_3613_);
lean_closure_set(v___y_3614_, 3, v___x_3605_);
lean_closure_set(v___y_3614_, 4, v___x_3606_);
lean_closure_set(v___y_3614_, 5, v___x_3607_);
lean_closure_set(v___y_3614_, 6, v___f_3611_);
v___x_3615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3615_, 0, v___y_3614_);
v___x_3616_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3615_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3628_, lean_object* v_as_3629_, lean_object* v_as_x27_3630_, lean_object* v_b_3631_, lean_object* v_a_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3628_, v_as_x27_3630_, v_b_3631_, v___y_3639_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3643_, lean_object* v_as_3644_, lean_object* v_as_x27_3645_, lean_object* v_b_3646_, lean_object* v_a_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3643_, v_as_3644_, v_as_x27_3645_, v_b_3646_, v_a_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v_as_3644_);
lean_dec(v___x_3643_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3665_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3665_, v___x_3666_, v___x_3667_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3699_ = l_Lean_addBuiltinDeclarationRanges(v___x_3697_, v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3702_, lean_object* v_simprocs_3703_, lean_object* v_fvarIdsToSimp_3704_, uint8_t v_simplifyTarget_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
v___x_3714_ = lean_unsigned_to_nat(32u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
lean_dec_ref(v___x_3715_);
v___x_3716_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
v___x_3717_ = l_Lean_Meta_dsimpGoal(v_a_3713_, v_ctx_3702_, v_simprocs_3703_, v_simplifyTarget_3705_, v_fvarIdsToSimp_3704_, v___x_3716_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_fst_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v_fst_3719_ = lean_ctor_get(v_a_3718_, 0);
if (lean_obj_tag(v_fst_3719_) == 0)
{
lean_object* v_snd_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_snd_3720_ = lean_ctor_get(v_a_3718_, 1);
lean_inc(v_snd_3720_);
lean_dec(v_a_3718_);
v___x_3721_ = lean_box(0);
v___x_3722_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3721_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v___x_3722_, 0);
lean_dec(v_unused_3730_);
v___x_3724_ = v___x_3722_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_dec(v___x_3722_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_snd_3720_);
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_snd_3720_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_snd_3720_);
v_a_3731_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3722_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3722_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v_snd_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3765_; 
lean_inc_ref(v_fst_3719_);
v_snd_3739_ = lean_ctor_get(v_a_3718_, 1);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3718_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v_a_3718_, 0);
lean_dec(v_unused_3766_);
v___x_3741_ = v_a_3718_;
v_isShared_3742_ = v_isSharedCheck_3765_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_snd_3739_);
lean_dec(v_a_3718_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3765_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v_val_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v_val_3743_ = lean_ctor_get(v_fst_3719_, 0);
lean_inc(v_val_3743_);
lean_dec_ref(v_fst_3719_);
v___x_3744_ = lean_box(0);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 1);
lean_ctor_set(v___x_3741_, 1, v___x_3744_);
lean_ctor_set(v___x_3741_, 0, v_val_3743_);
v___x_3746_ = v___x_3741_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_val_3743_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3746_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; 
v_unused_3755_ = lean_ctor_get(v___x_3747_, 0);
lean_dec(v_unused_3755_);
v___x_3749_ = v___x_3747_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v___x_3747_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v_snd_3739_);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_snd_3739_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v_snd_3739_);
v_a_3756_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3747_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3747_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
v_a_3767_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3717_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3717_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec_ref(v_fvarIdsToSimp_3704_);
lean_dec_ref(v_simprocs_3703_);
lean_dec_ref(v_ctx_3702_);
v_a_3775_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3712_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3712_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3783_, lean_object* v_simprocs_3784_, lean_object* v_fvarIdsToSimp_3785_, lean_object* v_simplifyTarget_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
uint8_t v_simplifyTarget_boxed_3793_; lean_object* v_res_3794_; 
v_simplifyTarget_boxed_3793_ = lean_unbox(v_simplifyTarget_3786_);
v_res_3794_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3783_, v_simprocs_3784_, v_fvarIdsToSimp_3785_, v_simplifyTarget_boxed_3793_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3787_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3795_, lean_object* v_simprocs_3796_, lean_object* v_fvarIdsToSimp_3797_, uint8_t v_simplifyTarget_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3795_, v_simprocs_3796_, v_fvarIdsToSimp_3797_, v_simplifyTarget_3798_, v_a_3800_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3809_, lean_object* v_simprocs_3810_, lean_object* v_fvarIdsToSimp_3811_, lean_object* v_simplifyTarget_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
uint8_t v_simplifyTarget_boxed_3822_; lean_object* v_res_3823_; 
v_simplifyTarget_boxed_3822_ = lean_unbox(v_simplifyTarget_3812_);
v_res_3823_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3809_, v_simprocs_3810_, v_fvarIdsToSimp_3811_, v_simplifyTarget_boxed_3822_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3824_, lean_object* v_simprocs_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3827_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3830_);
v___x_3837_ = l_Lean_MVarId_getNondepPropHyps(v_a_3836_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; uint8_t v___x_3839_; lean_object* v___x_3840_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = 1;
v___x_3840_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3824_, v_simprocs_3825_, v_a_3838_, v___x_3839_, v___y_3827_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3840_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_simprocs_3825_);
lean_dec_ref(v_ctx_3824_);
v_a_3841_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3837_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3837_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_simprocs_3825_);
lean_dec_ref(v_ctx_3824_);
v_a_3849_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3835_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3835_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3857_, lean_object* v_simprocs_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3857_, v_simprocs_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3869_, lean_object* v_ctx_3870_, lean_object* v_simprocs_3871_, uint8_t v_type_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3874_);
v___x_3882_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3869_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3870_, v_simprocs_3871_, v_a_3883_, v_type_3872_, v___y_3874_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3874_);
return v___x_3884_;
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec_ref(v_simprocs_3871_);
lean_dec_ref(v_ctx_3870_);
v_a_3885_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3882_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3882_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3893_, lean_object* v_ctx_3894_, lean_object* v_simprocs_3895_, lean_object* v_type_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v_type_643__boxed_3906_; lean_object* v_res_3907_; 
v_type_643__boxed_3906_ = lean_unbox(v_type_3896_);
v_res_3907_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3893_, v_ctx_3894_, v_simprocs_3895_, v_type_643__boxed_3906_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3908_, lean_object* v_simprocs_3909_, lean_object* v_loc_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
if (lean_obj_tag(v_loc_3910_) == 0)
{
lean_object* v___f_3920_; lean_object* v___x_3921_; 
v___f_3920_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3920_, 0, v_ctx_3908_);
lean_closure_set(v___f_3920_, 1, v_simprocs_3909_);
v___x_3921_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3920_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
return v___x_3921_;
}
else
{
lean_object* v_hypotheses_3922_; uint8_t v_type_3923_; lean_object* v___x_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; 
v_hypotheses_3922_ = lean_ctor_get(v_loc_3910_, 0);
lean_inc_ref(v_hypotheses_3922_);
v_type_3923_ = lean_ctor_get_uint8(v_loc_3910_, sizeof(void*)*1);
lean_dec_ref(v_loc_3910_);
v___x_3924_ = lean_box(v_type_3923_);
v___f_3925_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3925_, 0, v_hypotheses_3922_);
lean_closure_set(v___f_3925_, 1, v_ctx_3908_);
lean_closure_set(v___f_3925_, 2, v_simprocs_3909_);
lean_closure_set(v___f_3925_, 3, v___x_3924_);
v___x_3926_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3925_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3927_, lean_object* v_simprocs_3928_, lean_object* v_loc_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3927_, v_simprocs_3928_, v_loc_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3944_, lean_object* v_stx_3945_, uint8_t v___x_3946_, lean_object* v___x_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
if (v___x_3944_ == 0)
{
lean_object* v___x_3959_; 
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_3959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3959_;
}
else
{
lean_object* v___x_3960_; lean_object* v_tk_3961_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4046_; lean_object* v___y_4047_; uint8_t v___y_4048_; lean_object* v_stx_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; uint8_t v___y_4263_; lean_object* v___y_4264_; uint8_t v___y_4265_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; uint8_t v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; uint8_t v___y_4319_; lean_object* v_args_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___x_4341_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v_o_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v_bang_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_3960_ = lean_unsigned_to_nat(0u);
v_tk_3961_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3960_);
v___x_4341_ = lean_unsigned_to_nat(1u);
v___x_4398_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_4341_);
v___x_4399_ = l_Lean_Syntax_isNone(v___x_4398_);
if (v___x_4399_ == 0)
{
uint8_t v___x_4400_; 
lean_inc(v___x_4398_);
v___x_4400_ = l_Lean_Syntax_matchesNull(v___x_4398_, v___x_4341_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; 
lean_dec(v___x_4398_);
lean_dec(v_tk_3961_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4401_;
}
else
{
lean_object* v_bang_4402_; lean_object* v___x_4403_; 
v_bang_4402_ = l_Lean_Syntax_getArg(v___x_4398_, v___x_3960_);
lean_dec(v___x_4398_);
v___x_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4403_, 0, v_bang_4402_);
v_bang_4371_ = v___x_4403_;
v___y_4372_ = v___y_3950_;
v___y_4373_ = v___y_3951_;
v___y_4374_ = v___y_3952_;
v___y_4375_ = v___y_3953_;
v___y_4376_ = v___y_3954_;
v___y_4377_ = v___y_3955_;
v___y_4378_ = v___y_3956_;
v___y_4379_ = v___y_3957_;
goto v___jp_4370_;
}
}
else
{
lean_object* v___x_4404_; 
lean_dec(v___x_4398_);
v___x_4404_ = lean_box(0);
v_bang_4371_ = v___x_4404_;
v___y_4372_ = v___y_3950_;
v___y_4373_ = v___y_3951_;
v___y_4374_ = v___y_3952_;
v___y_4375_ = v___y_3953_;
v___y_4376_ = v___y_3954_;
v___y_4377_ = v___y_3955_;
v___y_4378_ = v___y_3956_;
v___y_4379_ = v___y_3957_;
goto v___jp_4370_;
}
v___jp_3962_:
{
lean_object* v___x_3975_; 
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3966_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3973_);
v___x_3975_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3965_, v___y_3968_, v___y_3974_, v___y_3972_, v___y_3970_, v___y_3963_, v___y_3967_, v___y_3973_, v___y_3969_, v___y_3966_, v___y_3971_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v_usedTheorems_3977_; lean_object* v_diag_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4019_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref(v___x_3975_);
v_usedTheorems_3977_ = lean_ctor_get(v_a_3976_, 0);
v_diag_3978_ = lean_ctor_get(v_a_3976_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_a_3976_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3980_ = v_a_3976_;
v_isShared_3981_ = v_isSharedCheck_4019_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_diag_3978_);
lean_inc(v_usedTheorems_3977_);
lean_dec(v_a_3976_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4019_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; 
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3966_);
v___x_3982_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3964_, v_usedTheorems_3977_, v___y_3973_, v___y_3969_, v___y_3966_, v___y_3971_);
lean_dec_ref(v_usedTheorems_3977_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v_ref_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v_ref_3984_ = lean_ctor_get(v___y_3966_, 5);
v___x_3985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v_a_3983_);
lean_ctor_set(v___x_3980_, 0, v___x_3985_);
v___x_3987_ = v___x_3980_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_a_3983_);
v___x_3987_ = v_reuseFailAlloc_4010_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3987_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
lean_ctor_set(v___x_3989_, 2, v___x_3988_);
lean_ctor_set(v___x_3989_, 3, v___x_3988_);
lean_ctor_set(v___x_3989_, 4, v___x_3988_);
lean_ctor_set(v___x_3989_, 5, v___x_3988_);
lean_inc(v_ref_3984_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_ref_3984_);
v___x_3991_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3992_ = 4;
v___x_3993_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3961_, v___x_3989_, v___x_3990_, v___x_3991_, v___x_3988_, v___x_3992_, v___y_3966_, v___y_3971_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; 
v_unused_4001_ = lean_ctor_get(v___x_3993_, 0);
lean_dec(v_unused_4001_);
v___x_3995_ = v___x_3993_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v___x_3993_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v_diag_3978_);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_diag_3978_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_diag_3978_);
v_a_4002_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3993_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3993_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_del_object(v___x_3980_);
lean_dec_ref(v_diag_3978_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3966_);
lean_dec(v_tk_3961_);
v_a_4011_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3982_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3982_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3971_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3964_);
lean_dec(v_tk_3961_);
v_a_4020_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_3975_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_3975_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
v___jp_4028_:
{
if (lean_obj_tag(v___y_4029_) == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4042_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
lean_ctor_set_uint8(v___x_4042_, sizeof(void*)*1, v___x_3946_);
v___y_3963_ = v___y_4030_;
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4040_;
v___y_3966_ = v___y_4032_;
v___y_3967_ = v___y_4033_;
v___y_3968_ = v___y_4034_;
v___y_3969_ = v___y_4036_;
v___y_3970_ = v___y_4035_;
v___y_3971_ = v___y_4038_;
v___y_3972_ = v___y_4037_;
v___y_3973_ = v___y_4039_;
v___y_3974_ = v___x_4042_;
goto v___jp_3962_;
}
else
{
lean_object* v_val_4043_; lean_object* v___x_4044_; 
v_val_4043_ = lean_ctor_get(v___y_4029_, 0);
lean_inc(v_val_4043_);
lean_dec_ref(v___y_4029_);
v___x_4044_ = l_Lean_Elab_Tactic_expandLocation(v_val_4043_);
lean_dec(v_val_4043_);
v___y_3963_ = v___y_4030_;
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4040_;
v___y_3966_ = v___y_4032_;
v___y_3967_ = v___y_4033_;
v___y_3968_ = v___y_4034_;
v___y_3969_ = v___y_4036_;
v___y_3970_ = v___y_4035_;
v___y_3971_ = v___y_4038_;
v___y_3972_ = v___y_4037_;
v___y_3973_ = v___y_4039_;
v___y_3974_ = v___x_4044_;
goto v___jp_3962_;
}
}
v___jp_4045_:
{
uint8_t v___x_4058_; uint8_t v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4058_ = 0;
v___x_4059_ = 2;
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4061_ = lean_box(v___x_4058_);
v___x_4062_ = lean_box(v___x_4059_);
v___x_4063_ = lean_box(v___x_4058_);
lean_inc(v_stx_4049_);
v___x_4064_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4064_, 0, v_stx_4049_);
lean_closure_set(v___x_4064_, 1, v___x_4061_);
lean_closure_set(v___x_4064_, 2, v___x_4062_);
lean_closure_set(v___x_4064_, 3, v___x_4063_);
lean_closure_set(v___x_4064_, 4, v___x_4060_);
lean_inc(v___y_4057_);
lean_inc_ref(v___y_4056_);
lean_inc(v___y_4055_);
lean_inc_ref(v___y_4054_);
lean_inc(v___y_4053_);
lean_inc_ref(v___y_4052_);
lean_inc(v___y_4051_);
lean_inc_ref(v___y_4050_);
v___x_4065_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4064_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref(v___x_4065_);
if (lean_obj_tag(v___y_4047_) == 0)
{
lean_object* v_ctx_4067_; lean_object* v_simprocs_4068_; 
v_ctx_4067_ = lean_ctor_get(v_a_4066_, 0);
lean_inc_ref(v_ctx_4067_);
v_simprocs_4068_ = lean_ctor_get(v_a_4066_, 1);
lean_inc_ref(v_simprocs_4068_);
lean_dec(v_a_4066_);
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4052_;
v___y_4031_ = v_stx_4049_;
v___y_4032_ = v___y_4056_;
v___y_4033_ = v___y_4053_;
v___y_4034_ = v_simprocs_4068_;
v___y_4035_ = v___y_4051_;
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___y_4050_;
v___y_4038_ = v___y_4057_;
v___y_4039_ = v___y_4054_;
v___y_4040_ = v_ctx_4067_;
goto v___jp_4028_;
}
else
{
lean_dec_ref(v___y_4047_);
if (v___y_4048_ == 0)
{
lean_object* v_ctx_4069_; lean_object* v_simprocs_4070_; 
v_ctx_4069_ = lean_ctor_get(v_a_4066_, 0);
lean_inc_ref(v_ctx_4069_);
v_simprocs_4070_ = lean_ctor_get(v_a_4066_, 1);
lean_inc_ref(v_simprocs_4070_);
lean_dec(v_a_4066_);
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4052_;
v___y_4031_ = v_stx_4049_;
v___y_4032_ = v___y_4056_;
v___y_4033_ = v___y_4053_;
v___y_4034_ = v_simprocs_4070_;
v___y_4035_ = v___y_4051_;
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___y_4050_;
v___y_4038_ = v___y_4057_;
v___y_4039_ = v___y_4054_;
v___y_4040_ = v_ctx_4069_;
goto v___jp_4028_;
}
else
{
lean_object* v_ctx_4071_; lean_object* v_simprocs_4072_; lean_object* v___x_4073_; 
v_ctx_4071_ = lean_ctor_get(v_a_4066_, 0);
lean_inc_ref(v_ctx_4071_);
v_simprocs_4072_ = lean_ctor_get(v_a_4066_, 1);
lean_inc_ref(v_simprocs_4072_);
lean_dec(v_a_4066_);
v___x_4073_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4071_);
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4052_;
v___y_4031_ = v_stx_4049_;
v___y_4032_ = v___y_4056_;
v___y_4033_ = v___y_4053_;
v___y_4034_ = v_simprocs_4072_;
v___y_4035_ = v___y_4051_;
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___y_4050_;
v___y_4038_ = v___y_4057_;
v___y_4039_ = v___y_4054_;
v___y_4040_ = v___x_4073_;
goto v___jp_4028_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v_stx_4049_);
lean_dec(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec(v_tk_3961_);
v_a_4074_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4065_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4065_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
v___jp_4082_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = l_Array_append___redArg(v___y_4093_, v___y_4103_);
lean_dec_ref(v___y_4103_);
lean_inc(v___y_4088_);
v___x_4105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4105_, 0, v___y_4088_);
lean_ctor_set(v___x_4105_, 1, v___y_4089_);
lean_ctor_set(v___x_4105_, 2, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_node6(v___y_4088_, v___y_4095_, v___y_4099_, v___y_4084_, v___y_4100_, v___y_4097_, v___y_4091_, v___x_4105_);
v___y_4046_ = v___y_4083_;
v___y_4047_ = v___y_4098_;
v___y_4048_ = v___y_4101_;
v_stx_4049_ = v___x_4106_;
v___y_4050_ = v___y_4087_;
v___y_4051_ = v___y_4096_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4086_;
v___y_4054_ = v___y_4094_;
v___y_4055_ = v___y_4090_;
v___y_4056_ = v___y_4102_;
v___y_4057_ = v___y_4092_;
goto v___jp_4045_;
}
v___jp_4107_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_inc_ref(v___y_4116_);
v___x_4128_ = l_Array_append___redArg(v___y_4116_, v___y_4127_);
lean_dec_ref(v___y_4127_);
lean_inc(v___y_4114_);
lean_inc(v___y_4113_);
v___x_4129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4129_, 0, v___y_4113_);
lean_ctor_set(v___x_4129_, 1, v___y_4114_);
lean_ctor_set(v___x_4129_, 2, v___x_4128_);
if (lean_obj_tag(v___y_4108_) == 0)
{
lean_object* v___x_4130_; 
v___x_4130_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4111_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4113_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4115_;
v___y_4091_ = v___x_4129_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4116_;
v___y_4094_ = v___y_4118_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___y_4121_;
v___y_4098_ = v___y_4122_;
v___y_4099_ = v___y_4124_;
v___y_4100_ = v___y_4123_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___x_4130_;
goto v___jp_4082_;
}
else
{
lean_object* v_val_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_val_4131_ = lean_ctor_get(v___y_4108_, 0);
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4131_);
v___x_4133_ = lean_array_push(v___x_4132_, v_val_4131_);
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4111_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4113_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4115_;
v___y_4091_ = v___x_4129_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4116_;
v___y_4094_ = v___y_4118_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___y_4121_;
v___y_4098_ = v___y_4122_;
v___y_4099_ = v___y_4124_;
v___y_4100_ = v___y_4123_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___x_4133_;
goto v___jp_4082_;
}
}
v___jp_4134_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_inc_ref(v___y_4144_);
v___x_4155_ = l_Array_append___redArg(v___y_4144_, v___y_4154_);
lean_dec_ref(v___y_4154_);
lean_inc(v___y_4142_);
lean_inc(v___y_4141_);
v___x_4156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4141_);
lean_ctor_set(v___x_4156_, 1, v___y_4142_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
if (lean_obj_tag(v___y_4139_) == 1)
{
lean_object* v_val_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_val_4157_ = lean_ctor_get(v___y_4139_, 0);
lean_inc(v_val_4157_);
lean_dec_ref(v___y_4139_);
v___x_4158_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_4141_);
v___x_4159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___y_4141_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
lean_inc_ref(v___y_4144_);
v___x_4160_ = l_Array_append___redArg(v___y_4144_, v_val_4157_);
lean_dec(v_val_4157_);
lean_inc(v___y_4142_);
lean_inc(v___y_4141_);
v___x_4161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4161_, 0, v___y_4141_);
lean_ctor_set(v___x_4161_, 1, v___y_4142_);
lean_ctor_set(v___x_4161_, 2, v___x_4160_);
v___x_4162_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_4141_);
v___x_4163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___y_4141_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = l_Array_mkArray3___redArg(v___x_4159_, v___x_4161_, v___x_4163_);
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___x_4156_;
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4152_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___x_4164_;
goto v___jp_4107_;
}
else
{
lean_object* v___x_4165_; 
lean_dec(v___y_4139_);
v___x_4165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___x_4156_;
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4152_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___x_4165_;
goto v___jp_4107_;
}
}
v___jp_4166_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = l_Array_append___redArg(v___y_4186_, v___y_4187_);
lean_dec_ref(v___y_4187_);
lean_inc(v___y_4170_);
v___x_4189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4189_, 0, v___y_4170_);
lean_ctor_set(v___x_4189_, 1, v___y_4174_);
lean_ctor_set(v___x_4189_, 2, v___x_4188_);
v___x_4190_ = l_Lean_Syntax_node6(v___y_4170_, v___y_4182_, v___y_4175_, v___y_4168_, v___y_4183_, v___y_4169_, v___y_4178_, v___x_4189_);
v___y_4046_ = v___y_4167_;
v___y_4047_ = v___y_4181_;
v___y_4048_ = v___y_4184_;
v_stx_4049_ = v___x_4190_;
v___y_4050_ = v___y_4173_;
v___y_4051_ = v___y_4180_;
v___y_4052_ = v___y_4171_;
v___y_4053_ = v___y_4172_;
v___y_4054_ = v___y_4179_;
v___y_4055_ = v___y_4176_;
v___y_4056_ = v___y_4185_;
v___y_4057_ = v___y_4177_;
goto v___jp_4045_;
}
v___jp_4191_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_inc_ref(v___y_4210_);
v___x_4212_ = l_Array_append___redArg(v___y_4210_, v___y_4211_);
lean_dec_ref(v___y_4211_);
lean_inc(v___y_4199_);
lean_inc(v___y_4195_);
v___x_4213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4213_, 0, v___y_4195_);
lean_ctor_set(v___x_4213_, 1, v___y_4199_);
lean_ctor_set(v___x_4213_, 2, v___x_4212_);
if (lean_obj_tag(v___y_4192_) == 0)
{
lean_object* v___x_4214_; 
v___x_4214_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4199_;
v___y_4175_ = v___y_4200_;
v___y_4176_ = v___y_4201_;
v___y_4177_ = v___y_4202_;
v___y_4178_ = v___x_4213_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___y_4206_;
v___y_4183_ = v___y_4207_;
v___y_4184_ = v___y_4208_;
v___y_4185_ = v___y_4209_;
v___y_4186_ = v___y_4210_;
v___y_4187_ = v___x_4214_;
goto v___jp_4166_;
}
else
{
lean_object* v_val_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_val_4215_ = lean_ctor_get(v___y_4192_, 0);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4215_);
v___x_4217_ = lean_array_push(v___x_4216_, v_val_4215_);
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4199_;
v___y_4175_ = v___y_4200_;
v___y_4176_ = v___y_4201_;
v___y_4177_ = v___y_4202_;
v___y_4178_ = v___x_4213_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___y_4206_;
v___y_4183_ = v___y_4207_;
v___y_4184_ = v___y_4208_;
v___y_4185_ = v___y_4209_;
v___y_4186_ = v___y_4210_;
v___y_4187_ = v___x_4217_;
goto v___jp_4166_;
}
}
v___jp_4218_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
lean_inc_ref(v___y_4237_);
v___x_4239_ = l_Array_append___redArg(v___y_4237_, v___y_4238_);
lean_dec_ref(v___y_4238_);
lean_inc(v___y_4226_);
lean_inc(v___y_4221_);
v___x_4240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4240_, 0, v___y_4221_);
lean_ctor_set(v___x_4240_, 1, v___y_4226_);
lean_ctor_set(v___x_4240_, 2, v___x_4239_);
if (lean_obj_tag(v___y_4224_) == 1)
{
lean_object* v_val_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_val_4241_ = lean_ctor_get(v___y_4224_, 0);
lean_inc(v_val_4241_);
lean_dec_ref(v___y_4224_);
v___x_4242_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc(v___y_4221_);
v___x_4243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___y_4221_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
lean_inc_ref(v___y_4237_);
v___x_4244_ = l_Array_append___redArg(v___y_4237_, v_val_4241_);
lean_dec(v_val_4241_);
lean_inc(v___y_4226_);
lean_inc(v___y_4221_);
v___x_4245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4245_, 0, v___y_4221_);
lean_ctor_set(v___x_4245_, 1, v___y_4226_);
lean_ctor_set(v___x_4245_, 2, v___x_4244_);
v___x_4246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
lean_inc(v___y_4221_);
v___x_4247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___y_4221_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l_Array_mkArray3___redArg(v___x_4243_, v___x_4245_, v___x_4247_);
v___y_4192_ = v___y_4219_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___x_4240_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4222_;
v___y_4197_ = v___y_4223_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4235_;
v___y_4209_ = v___y_4236_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___x_4248_;
goto v___jp_4191_;
}
else
{
lean_object* v___x_4249_; 
lean_dec(v___y_4224_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4192_ = v___y_4219_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___x_4240_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4222_;
v___y_4197_ = v___y_4223_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4235_;
v___y_4209_ = v___y_4236_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___x_4249_;
goto v___jp_4191_;
}
}
v___jp_4250_:
{
lean_object* v_ref_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_ref_4266_ = lean_ctor_get(v___y_4264_, 5);
v___x_4267_ = l_Lean_SourceInfo_fromRef(v_ref_4266_, v___y_4265_);
v___x_4268_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4269_ = l_Lean_Name_mkStr4(v___x_3947_, v___x_3948_, v___x_3949_, v___x_4268_);
v___x_4270_ = l_Lean_SourceInfo_fromRef(v_tk_3961_, v___x_3946_);
v___x_4271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
lean_ctor_set(v___x_4271_, 1, v___x_4268_);
v___x_4272_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4273_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4267_);
v___x_4274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4267_);
lean_ctor_set(v___x_4274_, 1, v___x_4272_);
lean_ctor_set(v___x_4274_, 2, v___x_4273_);
if (lean_obj_tag(v___y_4260_) == 1)
{
lean_object* v_val_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_val_4275_ = lean_ctor_get(v___y_4260_, 0);
lean_inc(v_val_4275_);
lean_dec_ref(v___y_4260_);
v___x_4276_ = l_Lean_SourceInfo_fromRef(v_val_4275_, v___x_3946_);
lean_dec(v_val_4275_);
v___x_4277_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = l_Array_mkArray1___redArg(v___x_4278_);
v___y_4135_ = v___y_4251_;
v___y_4136_ = v___y_4252_;
v___y_4137_ = v___y_4253_;
v___y_4138_ = v___y_4254_;
v___y_4139_ = v___y_4255_;
v___y_4140_ = v___y_4256_;
v___y_4141_ = v___x_4267_;
v___y_4142_ = v___x_4272_;
v___y_4143_ = v___y_4257_;
v___y_4144_ = v___x_4273_;
v___y_4145_ = v___y_4258_;
v___y_4146_ = v___y_4259_;
v___y_4147_ = v___x_4269_;
v___y_4148_ = v___y_4261_;
v___y_4149_ = v___y_4262_;
v___y_4150_ = v___x_4271_;
v___y_4151_ = v___x_4274_;
v___y_4152_ = v___y_4263_;
v___y_4153_ = v___y_4264_;
v___y_4154_ = v___x_4279_;
goto v___jp_4134_;
}
else
{
lean_object* v___x_4280_; 
lean_dec(v___y_4260_);
v___x_4280_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4135_ = v___y_4251_;
v___y_4136_ = v___y_4252_;
v___y_4137_ = v___y_4253_;
v___y_4138_ = v___y_4254_;
v___y_4139_ = v___y_4255_;
v___y_4140_ = v___y_4256_;
v___y_4141_ = v___x_4267_;
v___y_4142_ = v___x_4272_;
v___y_4143_ = v___y_4257_;
v___y_4144_ = v___x_4273_;
v___y_4145_ = v___y_4258_;
v___y_4146_ = v___y_4259_;
v___y_4147_ = v___x_4269_;
v___y_4148_ = v___y_4261_;
v___y_4149_ = v___y_4262_;
v___y_4150_ = v___x_4271_;
v___y_4151_ = v___x_4274_;
v___y_4152_ = v___y_4263_;
v___y_4153_ = v___y_4264_;
v___y_4154_ = v___x_4280_;
goto v___jp_4134_;
}
}
v___jp_4281_:
{
if (lean_obj_tag(v___y_4292_) == 0)
{
uint8_t v___x_4296_; 
v___x_4296_ = 0;
v___y_4251_ = v___y_4295_;
v___y_4252_ = v___y_4282_;
v___y_4253_ = v___y_4283_;
v___y_4254_ = v___y_4284_;
v___y_4255_ = v___y_4285_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4287_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___y_4290_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4292_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___x_4296_;
goto v___jp_4250_;
}
else
{
if (v___y_4293_ == 0)
{
v___y_4251_ = v___y_4295_;
v___y_4252_ = v___y_4282_;
v___y_4253_ = v___y_4283_;
v___y_4254_ = v___y_4284_;
v___y_4255_ = v___y_4285_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4287_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___y_4290_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4292_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___y_4293_;
goto v___jp_4250_;
}
else
{
lean_object* v_ref_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_ref_4297_ = lean_ctor_get(v___y_4294_, 5);
v___x_4298_ = 0;
v___x_4299_ = l_Lean_SourceInfo_fromRef(v_ref_4297_, v___x_4298_);
v___x_4300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4301_ = l_Lean_Name_mkStr4(v___x_3947_, v___x_3948_, v___x_3949_, v___x_4300_);
v___x_4302_ = l_Lean_SourceInfo_fromRef(v_tk_3961_, v___x_3946_);
v___x_4303_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4306_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4299_);
v___x_4307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4299_);
lean_ctor_set(v___x_4307_, 1, v___x_4305_);
lean_ctor_set(v___x_4307_, 2, v___x_4306_);
if (lean_obj_tag(v___y_4290_) == 1)
{
lean_object* v_val_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_val_4308_ = lean_ctor_get(v___y_4290_, 0);
lean_inc(v_val_4308_);
lean_dec_ref(v___y_4290_);
v___x_4309_ = l_Lean_SourceInfo_fromRef(v_val_4308_, v___x_3946_);
lean_dec(v_val_4308_);
v___x_4310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = l_Array_mkArray1___redArg(v___x_4311_);
v___y_4219_ = v___y_4295_;
v___y_4220_ = v___y_4282_;
v___y_4221_ = v___x_4299_;
v___y_4222_ = v___y_4283_;
v___y_4223_ = v___y_4284_;
v___y_4224_ = v___y_4285_;
v___y_4225_ = v___y_4286_;
v___y_4226_ = v___x_4305_;
v___y_4227_ = v___x_4304_;
v___y_4228_ = v___y_4287_;
v___y_4229_ = v___y_4288_;
v___y_4230_ = v___y_4289_;
v___y_4231_ = v___y_4291_;
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___x_4301_;
v___y_4234_ = v___x_4307_;
v___y_4235_ = v___y_4293_;
v___y_4236_ = v___y_4294_;
v___y_4237_ = v___x_4306_;
v___y_4238_ = v___x_4312_;
goto v___jp_4218_;
}
else
{
lean_object* v___x_4313_; 
lean_dec(v___y_4290_);
v___x_4313_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4219_ = v___y_4295_;
v___y_4220_ = v___y_4282_;
v___y_4221_ = v___x_4299_;
v___y_4222_ = v___y_4283_;
v___y_4223_ = v___y_4284_;
v___y_4224_ = v___y_4285_;
v___y_4225_ = v___y_4286_;
v___y_4226_ = v___x_4305_;
v___y_4227_ = v___x_4304_;
v___y_4228_ = v___y_4287_;
v___y_4229_ = v___y_4288_;
v___y_4230_ = v___y_4289_;
v___y_4231_ = v___y_4291_;
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___x_4301_;
v___y_4234_ = v___x_4307_;
v___y_4235_ = v___y_4293_;
v___y_4236_ = v___y_4294_;
v___y_4237_ = v___x_4306_;
v___y_4238_ = v___x_4313_;
goto v___jp_4218_;
}
}
}
}
v___jp_4314_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = lean_unsigned_to_nat(3u);
v___x_4330_ = l_Lean_Syntax_getArg(v___y_4316_, v___x_4329_);
lean_dec(v___y_4316_);
v___x_4331_ = l_Lean_Syntax_getOptional_x3f(v___x_4330_);
lean_dec(v___x_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_box(0);
v___y_4282_ = v___y_4315_;
v___y_4283_ = v___y_4323_;
v___y_4284_ = v___y_4324_;
v___y_4285_ = v_args_4320_;
v___y_4286_ = v___y_4321_;
v___y_4287_ = v___y_4326_;
v___y_4288_ = v___y_4328_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4317_;
v___y_4291_ = v___y_4322_;
v___y_4292_ = v___y_4318_;
v___y_4293_ = v___y_4319_;
v___y_4294_ = v___y_4327_;
v___y_4295_ = v___x_4332_;
goto v___jp_4281_;
}
else
{
lean_object* v_val_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
v_val_4333_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4331_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_val_4333_);
lean_dec(v___x_4331_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_val_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
v___y_4282_ = v___y_4315_;
v___y_4283_ = v___y_4323_;
v___y_4284_ = v___y_4324_;
v___y_4285_ = v_args_4320_;
v___y_4286_ = v___y_4321_;
v___y_4287_ = v___y_4326_;
v___y_4288_ = v___y_4328_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4317_;
v___y_4291_ = v___y_4322_;
v___y_4292_ = v___y_4318_;
v___y_4293_ = v___y_4319_;
v___y_4294_ = v___y_4327_;
v___y_4295_ = v___x_4338_;
goto v___jp_4281_;
}
}
}
}
v___jp_4342_:
{
lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4357_ = l_Lean_Syntax_getArg(v___y_4345_, v___y_4344_);
v___x_4358_ = l_Lean_Syntax_isNone(v___x_4357_);
if (v___x_4358_ == 0)
{
uint8_t v___x_4359_; 
lean_inc(v___x_4357_);
v___x_4359_ = l_Lean_Syntax_matchesNull(v___x_4357_, v___x_4341_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec(v___x_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v_o_4348_);
lean_dec(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec(v___y_4343_);
lean_dec(v_tk_3961_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4361_ = l_Lean_Syntax_getArg(v___x_4357_, v___x_3960_);
lean_dec(v___x_4357_);
v___x_4362_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
lean_inc_ref(v___x_3947_);
v___x_4363_ = l_Lean_Name_mkStr4(v___x_3947_, v___x_3948_, v___x_3949_, v___x_4362_);
lean_inc(v___x_4361_);
v___x_4364_ = l_Lean_Syntax_isOfKind(v___x_4361_, v___x_4363_);
lean_dec(v___x_4363_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; 
lean_dec(v___x_4361_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v_o_4348_);
lean_dec(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec(v___y_4343_);
lean_dec(v_tk_3961_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4365_;
}
else
{
lean_object* v___x_4366_; lean_object* v_args_4367_; lean_object* v___x_4368_; 
v___x_4366_ = l_Lean_Syntax_getArg(v___x_4361_, v___x_4341_);
lean_dec(v___x_4361_);
v_args_4367_ = l_Lean_Syntax_getArgs(v___x_4366_);
lean_dec(v___x_4366_);
v___x_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4368_, 0, v_args_4367_);
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4345_;
v___y_4317_ = v_o_4348_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v_args_4320_ = v___x_4368_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
v___y_4323_ = v___y_4351_;
v___y_4324_ = v___y_4352_;
v___y_4325_ = v___y_4353_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4356_;
goto v___jp_4314_;
}
}
}
else
{
lean_object* v___x_4369_; 
lean_dec(v___x_4357_);
v___x_4369_ = lean_box(0);
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4345_;
v___y_4317_ = v_o_4348_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v_args_4320_ = v___x_4369_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
v___y_4323_ = v___y_4351_;
v___y_4324_ = v___y_4352_;
v___y_4325_ = v___y_4353_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4356_;
goto v___jp_4314_;
}
}
v___jp_4370_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4380_ = lean_unsigned_to_nat(2u);
v___x_4381_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_4380_);
v___x_4382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
lean_inc_ref(v___x_3947_);
v___x_4383_ = l_Lean_Name_mkStr4(v___x_3947_, v___x_3948_, v___x_3949_, v___x_4382_);
lean_inc(v___x_4381_);
v___x_4384_ = l_Lean_Syntax_isOfKind(v___x_4381_, v___x_4383_);
lean_dec(v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
lean_dec(v___x_4381_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v_bang_4371_);
lean_dec(v_tk_3961_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4385_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4386_ = l_Lean_Syntax_getArg(v___x_4381_, v___x_3960_);
v___x_4387_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3949_);
lean_inc_ref(v___x_3948_);
lean_inc_ref(v___x_3947_);
v___x_4388_ = l_Lean_Name_mkStr4(v___x_3947_, v___x_3948_, v___x_3949_, v___x_4387_);
lean_inc(v___x_4386_);
v___x_4389_ = l_Lean_Syntax_isOfKind(v___x_4386_, v___x_4388_);
lean_dec(v___x_4388_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_dec(v___x_4386_);
lean_dec(v___x_4381_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v_bang_4371_);
lean_dec(v_tk_3961_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4390_;
}
else
{
lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4391_ = l_Lean_Syntax_getArg(v___x_4381_, v___x_4341_);
v___x_4392_ = l_Lean_Syntax_isNone(v___x_4391_);
if (v___x_4392_ == 0)
{
uint8_t v___x_4393_; 
lean_inc(v___x_4391_);
v___x_4393_ = l_Lean_Syntax_matchesNull(v___x_4391_, v___x_4341_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; 
lean_dec(v___x_4391_);
lean_dec(v___x_4386_);
lean_dec(v___x_4381_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v_bang_4371_);
lean_dec(v_tk_3961_);
lean_dec_ref(v___x_3949_);
lean_dec_ref(v___x_3948_);
lean_dec_ref(v___x_3947_);
v___x_4394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4394_;
}
else
{
lean_object* v_o_4395_; lean_object* v___x_4396_; 
v_o_4395_ = l_Lean_Syntax_getArg(v___x_4391_, v___x_3960_);
lean_dec(v___x_4391_);
v___x_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4396_, 0, v_o_4395_);
v___y_4343_ = v___x_4386_;
v___y_4344_ = v___x_4380_;
v___y_4345_ = v___x_4381_;
v___y_4346_ = v_bang_4371_;
v___y_4347_ = v___x_4389_;
v_o_4348_ = v___x_4396_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
v___y_4351_ = v___y_4374_;
v___y_4352_ = v___y_4375_;
v___y_4353_ = v___y_4376_;
v___y_4354_ = v___y_4377_;
v___y_4355_ = v___y_4378_;
v___y_4356_ = v___y_4379_;
goto v___jp_4342_;
}
}
else
{
lean_object* v___x_4397_; 
lean_dec(v___x_4391_);
v___x_4397_ = lean_box(0);
v___y_4343_ = v___x_4386_;
v___y_4344_ = v___x_4380_;
v___y_4345_ = v___x_4381_;
v___y_4346_ = v_bang_4371_;
v___y_4347_ = v___x_4389_;
v_o_4348_ = v___x_4397_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
v___y_4351_ = v___y_4374_;
v___y_4352_ = v___y_4375_;
v___y_4353_ = v___y_4376_;
v___y_4354_ = v___y_4377_;
v___y_4355_ = v___y_4378_;
v___y_4356_ = v___y_4379_;
goto v___jp_4342_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4405_, lean_object* v_stx_4406_, lean_object* v___x_4407_, lean_object* v___x_4408_, lean_object* v___x_4409_, lean_object* v___x_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
uint8_t v___x_10617__boxed_4420_; uint8_t v___x_10618__boxed_4421_; lean_object* v_res_4422_; 
v___x_10617__boxed_4420_ = lean_unbox(v___x_4405_);
v___x_10618__boxed_4421_ = lean_unbox(v___x_4407_);
v_res_4422_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10617__boxed_4420_, v_stx_4406_, v___x_10618__boxed_4421_, v___x_4408_, v___x_4409_, v___x_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v_stx_4406_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; uint8_t v___x_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___y_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4442_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4429_);
v___x_4443_ = l_Lean_Syntax_isOfKind(v_stx_4429_, v___x_4442_);
v___x_4444_ = 1;
v___x_4445_ = lean_box(v___x_4443_);
v___x_4446_ = lean_box(v___x_4444_);
v___y_4447_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4447_, 0, v___x_4445_);
lean_closure_set(v___y_4447_, 1, v_stx_4429_);
lean_closure_set(v___y_4447_, 2, v___x_4446_);
lean_closure_set(v___y_4447_, 3, v___x_4439_);
lean_closure_set(v___y_4447_, 4, v___x_4440_);
lean_closure_set(v___y_4447_, 5, v___x_4441_);
v___x_4448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4448_, 0, v___y_4447_);
v___x_4449_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4448_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4468_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4469_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4470_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4471_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4472_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4468_, v___x_4469_, v___x_4470_, v___x_4471_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4501_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4502_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4503_ = l_Lean_addBuiltinDeclarationRanges(v___x_4501_, v___x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4505_;
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
res = l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
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
