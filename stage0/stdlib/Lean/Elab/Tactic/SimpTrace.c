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
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_syntax_ident(lean_object*);
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
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_pre_49_);
lean_dec(v_pre_50_);
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
lean_dec(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v_pre_26_);
lean_dec(v_pre_27_);
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
uint8_t v___x_38752__boxed_208_; lean_object* v_res_209_; 
v___x_38752__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38752__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_38779__boxed_246_; lean_object* v_res_247_; 
v___x_38779__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_38779__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
lean_dec_ref(v___x_299_);
if (lean_obj_tag(v_val_301_) == 1)
{
uint8_t v_v_302_; 
v_v_302_ = lean_ctor_get_uint8(v_val_301_, 0);
lean_dec_ref(v_val_301_);
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
v_options_311_ = lean_ctor_get(v___y_309_, 2);
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
v_options_330_ = lean_ctor_get(v___y_322_, 2);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v___y_348_, uint8_t v_suppressElabErrors_349_, lean_object* v_x_350_){
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
return v___y_348_;
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_360_ = lean_string_dec_eq(v_str_353_, v___x_359_);
if (v___x_360_ == 0)
{
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
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
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
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
return v___y_348_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_370_ = lean_string_dec_eq(v_str_365_, v___x_369_);
if (v___x_370_ == 0)
{
return v___y_348_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_372_ = lean_string_dec_eq(v_str_364_, v___x_371_);
if (v___x_372_ == 0)
{
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
}
else
{
return v___y_348_;
}
}
default: 
{
return v___y_348_;
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
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
}
}
default: 
{
return v___y_348_;
}
}
}
else
{
return v___y_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v___y_376_, lean_object* v_suppressElabErrors_377_, lean_object* v_x_378_){
_start:
{
uint8_t v___y_38978__boxed_379_; uint8_t v_suppressElabErrors_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v___y_38978__boxed_379_ = lean_unbox(v___y_376_);
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_377_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v___y_38978__boxed_379_, v_suppressElabErrors_boxed_380_, v_x_378_);
lean_dec(v_x_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; uint8_t v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_430_; lean_object* v___y_431_; uint8_t v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v___y_471_; uint8_t v___y_472_; uint8_t v___x_477_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; uint8_t v___y_485_; uint8_t v___y_487_; uint8_t v___x_502_; 
v___x_477_ = 2;
v___x_502_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_477_);
if (v___x_502_ == 0)
{
v___y_487_ = v___x_502_;
goto v___jp_486_;
}
else
{
uint8_t v___x_503_; 
lean_inc_ref(v_msgData_385_);
v___x_503_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_385_);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
v___jp_393_:
{
lean_object* v___x_403_; lean_object* v_currNamespace_404_; lean_object* v_openDecls_405_; lean_object* v_env_406_; lean_object* v_nextMacroScope_407_; lean_object* v_ngen_408_; lean_object* v_auxDeclNGen_409_; lean_object* v_traceState_410_; lean_object* v_cache_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_428_; 
v___x_403_ = lean_st_ref_take(v___y_402_);
v_currNamespace_404_ = lean_ctor_get(v___y_401_, 6);
v_openDecls_405_ = lean_ctor_get(v___y_401_, 7);
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
lean_ctor_set(v___x_419_, 1, v___y_398_);
lean_inc_ref(v___y_396_);
lean_inc_ref(v___y_399_);
v___x_420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_420_, 0, v___y_399_);
lean_ctor_set(v___x_420_, 1, v___y_394_);
lean_ctor_set(v___x_420_, 2, v___y_395_);
lean_ctor_set(v___x_420_, 3, v___y_396_);
lean_ctor_set(v___x_420_, 4, v___x_419_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5, v___y_397_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5 + 1, v___y_400_);
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
v___x_424_ = lean_st_ref_set(v___y_402_, v___x_423_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
v___jp_429_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_453_; 
v___x_438_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_385_);
v___x_439_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_438_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_453_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_inc_ref_n(v___y_433_, 2);
v___x_444_ = l_Lean_FileMap_toPosition(v___y_433_, v___y_431_);
lean_dec(v___y_431_);
v___x_445_ = l_Lean_FileMap_toPosition(v___y_433_, v___y_437_);
lean_dec(v___y_437_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_434_ == 0)
{
lean_del_object(v___x_442_);
lean_dec_ref(v___y_430_);
v___y_394_ = v___x_444_;
v___y_395_ = v___x_446_;
v___y_396_ = v___x_447_;
v___y_397_ = v___y_432_;
v___y_398_ = v_a_440_;
v___y_399_ = v___y_435_;
v___y_400_ = v___y_436_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
else
{
uint8_t v___x_448_; 
lean_inc(v_a_440_);
v___x_448_ = l_Lean_MessageData_hasTag(v___y_430_, v_a_440_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec_ref(v___x_446_);
lean_dec_ref(v___x_444_);
lean_dec(v_a_440_);
v___x_449_ = lean_box(0);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_449_);
v___x_451_ = v___x_442_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_del_object(v___x_442_);
v___y_394_ = v___x_444_;
v___y_395_ = v___x_446_;
v___y_396_ = v___x_447_;
v___y_397_ = v___y_432_;
v___y_398_ = v_a_440_;
v___y_399_ = v___y_435_;
v___y_400_ = v___y_436_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
}
}
}
v___jp_454_:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Syntax_getTailPos_x3f(v___y_458_, v___y_456_);
lean_dec(v___y_458_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_inc(v___y_462_);
v___y_430_ = v___y_455_;
v___y_431_ = v___y_462_;
v___y_432_ = v___y_456_;
v___y_433_ = v___y_457_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_462_;
goto v___jp_429_;
}
else
{
lean_object* v_val_464_; 
v_val_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_464_);
lean_dec_ref(v___x_463_);
v___y_430_ = v___y_455_;
v___y_431_ = v___y_462_;
v___y_432_ = v___y_456_;
v___y_433_ = v___y_457_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_461_;
v___y_437_ = v_val_464_;
goto v___jp_429_;
}
}
v___jp_465_:
{
lean_object* v_ref_473_; lean_object* v___x_474_; 
v_ref_473_ = l_Lean_replaceRef(v_ref_384_, v___y_468_);
v___x_474_ = l_Lean_Syntax_getPos_x3f(v_ref_473_, v___y_467_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___y_455_ = v___y_466_;
v___y_456_ = v___y_467_;
v___y_457_ = v___y_469_;
v___y_458_ = v_ref_473_;
v___y_459_ = v___y_470_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_472_;
v___y_462_ = v___x_475_;
goto v___jp_454_;
}
else
{
lean_object* v_val_476_; 
v_val_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v___x_474_);
v___y_455_ = v___y_466_;
v___y_456_ = v___y_467_;
v___y_457_ = v___y_469_;
v___y_458_ = v_ref_473_;
v___y_459_ = v___y_470_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_472_;
v___y_462_ = v_val_476_;
goto v___jp_454_;
}
}
v___jp_478_:
{
if (v___y_485_ == 0)
{
v___y_466_ = v___y_479_;
v___y_467_ = v___y_484_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_481_;
v___y_470_ = v___y_482_;
v___y_471_ = v___y_483_;
v___y_472_ = v_severity_386_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___y_479_;
v___y_467_ = v___y_484_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_481_;
v___y_470_ = v___y_482_;
v___y_471_ = v___y_483_;
v___y_472_ = v___x_477_;
goto v___jp_465_;
}
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v_fileName_488_; lean_object* v_fileMap_489_; lean_object* v_options_490_; lean_object* v_ref_491_; uint8_t v_suppressElabErrors_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___f_495_; uint8_t v___x_496_; uint8_t v___x_497_; 
v_fileName_488_ = lean_ctor_get(v___y_390_, 0);
v_fileMap_489_ = lean_ctor_get(v___y_390_, 1);
v_options_490_ = lean_ctor_get(v___y_390_, 2);
v_ref_491_ = lean_ctor_get(v___y_390_, 5);
v_suppressElabErrors_492_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*14 + 1);
v___x_493_ = lean_box(v___y_487_);
v___x_494_ = lean_box(v_suppressElabErrors_492_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_495_, 0, v___x_493_);
lean_closure_set(v___f_495_, 1, v___x_494_);
v___x_496_ = 1;
v___x_497_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_479_ = v___f_495_;
v___y_480_ = v_ref_491_;
v___y_481_ = v_fileMap_489_;
v___y_482_ = v_suppressElabErrors_492_;
v___y_483_ = v_fileName_488_;
v___y_484_ = v___y_487_;
v___y_485_ = v___x_497_;
goto v___jp_478_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = l_Lean_warningAsError;
v___x_499_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_490_, v___x_498_);
v___y_479_ = v___f_495_;
v___y_480_ = v_ref_491_;
v___y_481_ = v_fileMap_489_;
v___y_482_ = v_suppressElabErrors_492_;
v___y_483_ = v_fileName_488_;
v___y_484_ = v___y_487_;
v___y_485_ = v___x_499_;
goto v___jp_478_;
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v_msgData_385_);
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_504_, lean_object* v_msgData_505_, lean_object* v_severity_506_, lean_object* v_isSilent_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v_severity_boxed_513_; uint8_t v_isSilent_boxed_514_; lean_object* v_res_515_; 
v_severity_boxed_513_ = lean_unbox(v_severity_506_);
v_isSilent_boxed_514_ = lean_unbox(v_isSilent_507_);
v_res_515_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_504_, v_msgData_505_, v_severity_boxed_513_, v_isSilent_boxed_514_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v_ref_504_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_516_, uint8_t v_severity_517_, uint8_t v_isSilent_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_ref_528_; lean_object* v___x_529_; 
v_ref_528_ = lean_ctor_get(v___y_525_, 5);
v___x_529_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_528_, v_msgData_516_, v_severity_517_, v_isSilent_518_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_530_, lean_object* v_severity_531_, lean_object* v_isSilent_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v_severity_boxed_542_; uint8_t v_isSilent_boxed_543_; lean_object* v_res_544_; 
v_severity_boxed_542_ = lean_unbox(v_severity_531_);
v_isSilent_boxed_543_ = lean_unbox(v_isSilent_532_);
v_res_544_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_530_, v_severity_boxed_542_, v_isSilent_boxed_543_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = 1;
v___x_556_ = 0;
v___x_557_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_545_, v___x_555_, v___x_556_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_env_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_608_; 
v___x_585_ = lean_st_ref_get(v___y_583_);
v_env_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_585_);
v___x_587_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_588_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_587_, v___y_582_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_608_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_608_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_608_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v_isExporting_598_; 
v_isExporting_598_ = lean_ctor_get_uint8(v_env_586_, sizeof(void*)*8);
lean_dec_ref(v_env_586_);
if (v_isExporting_598_ == 0)
{
lean_dec(v_a_589_);
lean_dec(v_id_575_);
goto v___jp_593_;
}
else
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_isPrivateName(v_id_575_);
if (v___x_599_ == 0)
{
lean_dec(v_a_589_);
lean_dec(v_id_575_);
goto v___jp_593_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_589_);
lean_dec(v_a_589_);
if (v___x_600_ == 0)
{
lean_dec(v_id_575_);
goto v___jp_593_;
}
else
{
lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_del_object(v___x_591_);
v___x_601_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_602_ = 0;
v___x_603_ = l_Lean_MessageData_ofConstName(v_id_575_, v___x_602_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_606_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_607_;
}
}
}
v___jp_593_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_594_);
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_620_, uint8_t v_enableLog_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_env_632_; lean_object* v_options_633_; lean_object* v_currNamespace_634_; lean_object* v_openDecls_635_; lean_object* v___x_636_; lean_object* v_env_637_; lean_object* v_res_638_; 
v___x_631_ = lean_st_ref_get(v___y_629_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v_options_633_ = lean_ctor_get(v___y_628_, 2);
v_currNamespace_634_ = lean_ctor_get(v___y_628_, 6);
v_openDecls_635_ = lean_ctor_get(v___y_628_, 7);
v___x_636_ = lean_st_ref_get(v___y_629_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
lean_inc(v_openDecls_635_);
lean_inc(v_currNamespace_634_);
v_res_638_ = l_Lean_ResolveName_resolveGlobalName(v_env_632_, v_options_633_, v_currNamespace_634_, v_openDecls_635_, v_id_620_);
if (v_enableLog_621_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_env_637_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_res_638_);
return v___x_639_;
}
else
{
uint8_t v_isExporting_640_; 
v_isExporting_640_ = lean_ctor_get_uint8(v_env_637_, sizeof(void*)*8);
lean_dec_ref(v_env_637_);
if (v_isExporting_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_res_638_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_638_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v_fst_644_; lean_object* v___x_645_; 
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref(v___x_642_);
v_fst_644_ = lean_ctor_get(v_val_643_, 0);
lean_inc(v_fst_644_);
lean_dec(v_val_643_);
v___x_645_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_644_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_653_);
v___x_647_ = v___x_645_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_645_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v_res_638_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_res_638_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_res_638_);
v_a_654_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_645_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_645_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v___x_662_; 
lean_dec(v___x_642_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_res_638_);
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_663_, lean_object* v_enableLog_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v_enableLog_boxed_674_; lean_object* v_res_675_; 
v_enableLog_boxed_674_ = lean_unbox(v_enableLog_664_);
v_res_675_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_663_, v_enableLog_boxed_674_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
if (lean_obj_tag(v_a_676_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_List_reverse___redArg(v_a_677_);
return v___x_678_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_691_; 
v_head_679_ = lean_ctor_get(v_a_676_, 0);
v_tail_680_ = lean_ctor_get(v_a_676_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_691_ == 0)
{
v___x_682_ = v_a_676_;
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_a_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_snd_684_; uint8_t v___x_685_; 
v_snd_684_ = lean_ctor_get(v_head_679_, 1);
v___x_685_ = l_List_isEmpty___redArg(v_snd_684_);
if (v___x_685_ == 0)
{
lean_del_object(v___x_682_);
lean_dec(v_head_679_);
v_a_676_ = v_tail_680_;
goto _start;
}
else
{
lean_object* v___x_688_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_a_677_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_head_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_a_677_);
v___x_688_ = v_reuseFailAlloc_690_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_a_676_ = v_tail_680_;
v_a_677_ = v___x_688_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
if (lean_obj_tag(v_a_692_) == 0)
{
lean_object* v___x_694_; 
v___x_694_ = l_List_reverse___redArg(v_a_693_);
return v___x_694_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_705_; 
v_head_695_ = lean_ctor_get(v_a_692_, 0);
v_tail_696_ = lean_ctor_get(v_a_692_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_705_ == 0)
{
v___x_698_ = v_a_692_;
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_tail_696_);
lean_inc(v_head_695_);
lean_dec(v_a_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_fst_700_; lean_object* v___x_702_; 
v_fst_700_ = lean_ctor_get(v_head_695_, 0);
lean_inc(v_fst_700_);
lean_dec(v_head_695_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_a_693_);
lean_ctor_set(v___x_698_, 0, v_fst_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_fst_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_693_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v_a_692_ = v_tail_696_;
v_a_693_ = v___x_702_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_ref_712_; lean_object* v___x_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_ref_712_ = lean_ctor_get(v___y_709_, 5);
v___x_713_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_inc(v_ref_712_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_ref_712_);
lean_ctor_set(v___x_718_, 1, v_a_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 1);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_730_, lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_fileName_741_; lean_object* v_fileMap_742_; lean_object* v_options_743_; lean_object* v_currRecDepth_744_; lean_object* v_maxRecDepth_745_; lean_object* v_ref_746_; lean_object* v_currNamespace_747_; lean_object* v_openDecls_748_; lean_object* v_initHeartbeats_749_; lean_object* v_maxHeartbeats_750_; lean_object* v_quotContext_751_; lean_object* v_currMacroScope_752_; uint8_t v_diag_753_; lean_object* v_cancelTk_x3f_754_; uint8_t v_suppressElabErrors_755_; lean_object* v_inheritedTraceOptions_756_; lean_object* v_ref_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_fileName_741_ = lean_ctor_get(v___y_738_, 0);
v_fileMap_742_ = lean_ctor_get(v___y_738_, 1);
v_options_743_ = lean_ctor_get(v___y_738_, 2);
v_currRecDepth_744_ = lean_ctor_get(v___y_738_, 3);
v_maxRecDepth_745_ = lean_ctor_get(v___y_738_, 4);
v_ref_746_ = lean_ctor_get(v___y_738_, 5);
v_currNamespace_747_ = lean_ctor_get(v___y_738_, 6);
v_openDecls_748_ = lean_ctor_get(v___y_738_, 7);
v_initHeartbeats_749_ = lean_ctor_get(v___y_738_, 8);
v_maxHeartbeats_750_ = lean_ctor_get(v___y_738_, 9);
v_quotContext_751_ = lean_ctor_get(v___y_738_, 10);
v_currMacroScope_752_ = lean_ctor_get(v___y_738_, 11);
v_diag_753_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*14);
v_cancelTk_x3f_754_ = lean_ctor_get(v___y_738_, 12);
v_suppressElabErrors_755_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_756_ = lean_ctor_get(v___y_738_, 13);
v_ref_757_ = l_Lean_replaceRef(v_ref_730_, v_ref_746_);
lean_inc_ref(v_inheritedTraceOptions_756_);
lean_inc(v_cancelTk_x3f_754_);
lean_inc(v_currMacroScope_752_);
lean_inc(v_quotContext_751_);
lean_inc(v_maxHeartbeats_750_);
lean_inc(v_initHeartbeats_749_);
lean_inc(v_openDecls_748_);
lean_inc(v_currNamespace_747_);
lean_inc(v_maxRecDepth_745_);
lean_inc(v_currRecDepth_744_);
lean_inc_ref(v_options_743_);
lean_inc_ref(v_fileMap_742_);
lean_inc_ref(v_fileName_741_);
v___x_758_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_758_, 0, v_fileName_741_);
lean_ctor_set(v___x_758_, 1, v_fileMap_742_);
lean_ctor_set(v___x_758_, 2, v_options_743_);
lean_ctor_set(v___x_758_, 3, v_currRecDepth_744_);
lean_ctor_set(v___x_758_, 4, v_maxRecDepth_745_);
lean_ctor_set(v___x_758_, 5, v_ref_757_);
lean_ctor_set(v___x_758_, 6, v_currNamespace_747_);
lean_ctor_set(v___x_758_, 7, v_openDecls_748_);
lean_ctor_set(v___x_758_, 8, v_initHeartbeats_749_);
lean_ctor_set(v___x_758_, 9, v_maxHeartbeats_750_);
lean_ctor_set(v___x_758_, 10, v_quotContext_751_);
lean_ctor_set(v___x_758_, 11, v_currMacroScope_752_);
lean_ctor_set(v___x_758_, 12, v_cancelTk_x3f_754_);
lean_ctor_set(v___x_758_, 13, v_inheritedTraceOptions_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*14, v_diag_753_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*14 + 1, v_suppressElabErrors_755_);
v___x_759_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_731_, v___y_736_, v___y_737_, v___x_758_, v___y_739_);
lean_dec_ref(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_760_, v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v_ref_760_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
lean_ctor_set(v___x_777_, 3, v___x_776_);
lean_ctor_set(v___x_777_, 4, v___x_775_);
lean_ctor_set(v___x_777_, 5, v___x_775_);
lean_ctor_set(v___x_777_, 6, v___x_775_);
lean_ctor_set(v___x_777_, 7, v___x_775_);
lean_ctor_set(v___x_777_, 8, v___x_775_);
lean_ctor_set(v___x_777_, 9, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(32u);
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_781_ = ((size_t)5ULL);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_unsigned_to_nat(32u);
v___x_784_ = lean_mk_empty_array_with_capacity(v___x_783_);
v___x_785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_786_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_782_);
lean_ctor_set(v___x_786_, 3, v___x_782_);
lean_ctor_set_usize(v___x_786_, 4, v___x_781_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_787_ = lean_box(1);
v___x_788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
lean_ctor_set(v___x_790_, 2, v___x_787_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_812_, lean_object* v_declHint_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; lean_object* v_env_817_; uint8_t v___x_818_; 
v___x_816_ = lean_st_ref_get(v___y_814_);
v_env_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_env_817_);
lean_dec(v___x_816_);
v___x_818_ = l_Lean_Name_isAnonymous(v_declHint_813_);
if (v___x_818_ == 0)
{
uint8_t v_isExporting_819_; 
v_isExporting_819_ = lean_ctor_get_uint8(v_env_817_, sizeof(void*)*8);
if (v_isExporting_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec_ref(v_env_817_);
lean_dec(v_declHint_813_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_msg_812_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
lean_inc_ref(v_env_817_);
v___x_821_ = l_Lean_Environment_setExporting(v_env_817_, v___x_818_);
lean_inc(v_declHint_813_);
lean_inc_ref(v___x_821_);
v___x_822_ = l_Lean_Environment_contains(v___x_821_, v_declHint_813_, v_isExporting_819_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v___x_821_);
lean_dec_ref(v_env_817_);
lean_dec(v_declHint_813_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v_msg_812_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_c_829_; lean_object* v___x_830_; 
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_826_ = l_Lean_Options_empty;
v___x_827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_827_, 0, v___x_821_);
lean_ctor_set(v___x_827_, 1, v___x_824_);
lean_ctor_set(v___x_827_, 2, v___x_825_);
lean_ctor_set(v___x_827_, 3, v___x_826_);
lean_inc(v_declHint_813_);
v___x_828_ = l_Lean_MessageData_ofConstName(v_declHint_813_, v___x_818_);
v_c_829_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_829_, 0, v___x_827_);
lean_ctor_set(v_c_829_, 1, v___x_828_);
v___x_830_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_817_, v_declHint_813_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_env_817_);
lean_dec(v_declHint_813_);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_c_829_);
v___x_833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_MessageData_note(v___x_834_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v_msg_812_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v_val_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_873_; 
v_val_838_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_873_ == 0)
{
v___x_840_ = v___x_830_;
v_isShared_841_ = v_isSharedCheck_873_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_val_838_);
lean_dec(v___x_830_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_873_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_mod_845_; uint8_t v___x_846_; 
v___x_842_ = lean_box(0);
v___x_843_ = l_Lean_Environment_header(v_env_817_);
lean_dec_ref(v_env_817_);
v___x_844_ = l_Lean_EnvironmentHeader_moduleNames(v___x_843_);
v_mod_845_ = lean_array_get(v___x_842_, v___x_844_, v_val_838_);
lean_dec(v_val_838_);
lean_dec_ref(v___x_844_);
v___x_846_ = l_Lean_isPrivateName(v_declHint_813_);
lean_dec(v_declHint_813_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_c_829_);
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_MessageData_ofName(v_mod_845_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_MessageData_note(v___x_854_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v_msg_812_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 0);
lean_ctor_set(v___x_840_, 0, v___x_856_);
v___x_858_ = v___x_840_;
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
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_c_829_);
v___x_862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_MessageData_ofName(v_mod_845_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_MessageData_note(v___x_867_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v_msg_812_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 0);
lean_ctor_set(v___x_840_, 0, v___x_869_);
v___x_871_ = v___x_840_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v_env_817_);
lean_dec(v_declHint_813_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_msg_812_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_875_, lean_object* v_declHint_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_875_, v_declHint_876_, v___y_877_);
lean_dec(v___y_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_880_, lean_object* v_declHint_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_901_; 
v___x_891_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_880_, v_declHint_881_, v___y_889_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_901_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_896_ = l_Lean_unknownIdentifierMessageTag;
v___x_897_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_902_, v_declHint_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_914_, lean_object* v_msg_915_, lean_object* v_declHint_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_928_; 
v___x_926_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_915_, v_declHint_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_914_, v_a_927_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_929_, lean_object* v_msg_930_, lean_object* v_declHint_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_929_, v_msg_930_, v_declHint_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v_ref_929_);
return v_res_941_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_948_, lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_959_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_960_ = 0;
lean_inc(v_constName_949_);
v___x_961_ = l_Lean_MessageData_ofConstName(v_constName_949_, v___x_960_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_959_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_948_, v___x_964_, v_constName_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_966_, lean_object* v_constName_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_966_, v_constName_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_ref_966_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_978_, lean_object* v_cs_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v_cs_990_; uint8_t v___x_994_; 
v___x_989_ = lean_box(0);
v_cs_990_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_979_, v___x_989_);
v___x_994_ = l_List_isEmpty___redArg(v_cs_990_);
if (v___x_994_ == 0)
{
lean_dec(v_n_978_);
goto v___jp_991_;
}
else
{
lean_object* v_ref_995_; lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_cs_990_);
v_ref_995_ = lean_ctor_get(v___y_986_, 5);
v___x_996_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_995_, v_n_978_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
v___jp_991_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_990_, v___x_989_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1005_, lean_object* v_cs_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1005_, v_cs_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = 1;
lean_inc(v_n_1017_);
v___x_1028_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1017_, v___x_1027_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1017_, v_a_1029_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1030_;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_n_1017_);
v_a_1031_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1028_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1028_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
if (lean_obj_tag(v_a_1050_) == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_array_to_list(v_a_1051_);
return v___x_1052_;
}
else
{
lean_object* v_head_1053_; 
v_head_1053_ = lean_ctor_get(v_a_1050_, 0);
if (lean_obj_tag(v_head_1053_) == 1)
{
lean_object* v_fields_1054_; 
v_fields_1054_ = lean_ctor_get(v_head_1053_, 1);
if (lean_obj_tag(v_fields_1054_) == 0)
{
lean_object* v_tail_1055_; lean_object* v_n_1056_; lean_object* v___x_1057_; 
lean_inc_ref(v_head_1053_);
v_tail_1055_ = lean_ctor_get(v_a_1050_, 1);
lean_inc(v_tail_1055_);
lean_dec_ref(v_a_1050_);
v_n_1056_ = lean_ctor_get(v_head_1053_, 0);
lean_inc(v_n_1056_);
lean_dec_ref(v_head_1053_);
v___x_1057_ = lean_array_push(v_a_1051_, v_n_1056_);
v_a_1050_ = v_tail_1055_;
v_a_1051_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v_tail_1059_; 
v_tail_1059_ = lean_ctor_get(v_a_1050_, 1);
lean_inc(v_tail_1059_);
lean_dec_ref(v_a_1050_);
v_a_1050_ = v_tail_1059_;
goto _start;
}
}
else
{
lean_object* v_tail_1061_; 
v_tail_1061_ = lean_ctor_get(v_a_1050_, 1);
lean_inc(v_tail_1061_);
lean_dec_ref(v_a_1050_);
v_a_1050_ = v_tail_1061_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1070_, lean_object* v_k_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
if (lean_obj_tag(v_stx_1070_) == 3)
{
lean_object* v_val_1081_; lean_object* v_preresolved_1082_; lean_object* v___x_1083_; lean_object* v_pre_1084_; uint8_t v___x_1085_; 
v_val_1081_ = lean_ctor_get(v_stx_1070_, 2);
lean_inc(v_val_1081_);
v_preresolved_1082_ = lean_ctor_get(v_stx_1070_, 3);
v___x_1083_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1082_);
v_pre_1084_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1082_, v___x_1083_);
v___x_1085_ = l_List_isEmpty___redArg(v_pre_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_val_1081_);
lean_dec_ref(v_stx_1070_);
lean_dec_ref(v_k_1071_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_pre_1084_);
return v___x_1086_;
}
else
{
lean_object* v_fileName_1087_; lean_object* v_fileMap_1088_; lean_object* v_options_1089_; lean_object* v_currRecDepth_1090_; lean_object* v_maxRecDepth_1091_; lean_object* v_ref_1092_; lean_object* v_currNamespace_1093_; lean_object* v_openDecls_1094_; lean_object* v_initHeartbeats_1095_; lean_object* v_maxHeartbeats_1096_; lean_object* v_quotContext_1097_; lean_object* v_currMacroScope_1098_; uint8_t v_diag_1099_; lean_object* v_cancelTk_x3f_1100_; uint8_t v_suppressElabErrors_1101_; lean_object* v_inheritedTraceOptions_1102_; lean_object* v_ref_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_pre_1084_);
v_fileName_1087_ = lean_ctor_get(v___y_1078_, 0);
v_fileMap_1088_ = lean_ctor_get(v___y_1078_, 1);
v_options_1089_ = lean_ctor_get(v___y_1078_, 2);
v_currRecDepth_1090_ = lean_ctor_get(v___y_1078_, 3);
v_maxRecDepth_1091_ = lean_ctor_get(v___y_1078_, 4);
v_ref_1092_ = lean_ctor_get(v___y_1078_, 5);
v_currNamespace_1093_ = lean_ctor_get(v___y_1078_, 6);
v_openDecls_1094_ = lean_ctor_get(v___y_1078_, 7);
v_initHeartbeats_1095_ = lean_ctor_get(v___y_1078_, 8);
v_maxHeartbeats_1096_ = lean_ctor_get(v___y_1078_, 9);
v_quotContext_1097_ = lean_ctor_get(v___y_1078_, 10);
v_currMacroScope_1098_ = lean_ctor_get(v___y_1078_, 11);
v_diag_1099_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*14);
v_cancelTk_x3f_1100_ = lean_ctor_get(v___y_1078_, 12);
v_suppressElabErrors_1101_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1102_ = lean_ctor_get(v___y_1078_, 13);
v_ref_1103_ = l_Lean_replaceRef(v_stx_1070_, v_ref_1092_);
lean_dec_ref(v_stx_1070_);
lean_inc_ref(v_inheritedTraceOptions_1102_);
lean_inc(v_cancelTk_x3f_1100_);
lean_inc(v_currMacroScope_1098_);
lean_inc(v_quotContext_1097_);
lean_inc(v_maxHeartbeats_1096_);
lean_inc(v_initHeartbeats_1095_);
lean_inc(v_openDecls_1094_);
lean_inc(v_currNamespace_1093_);
lean_inc(v_maxRecDepth_1091_);
lean_inc(v_currRecDepth_1090_);
lean_inc_ref(v_options_1089_);
lean_inc_ref(v_fileMap_1088_);
lean_inc_ref(v_fileName_1087_);
v___x_1104_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1104_, 0, v_fileName_1087_);
lean_ctor_set(v___x_1104_, 1, v_fileMap_1088_);
lean_ctor_set(v___x_1104_, 2, v_options_1089_);
lean_ctor_set(v___x_1104_, 3, v_currRecDepth_1090_);
lean_ctor_set(v___x_1104_, 4, v_maxRecDepth_1091_);
lean_ctor_set(v___x_1104_, 5, v_ref_1103_);
lean_ctor_set(v___x_1104_, 6, v_currNamespace_1093_);
lean_ctor_set(v___x_1104_, 7, v_openDecls_1094_);
lean_ctor_set(v___x_1104_, 8, v_initHeartbeats_1095_);
lean_ctor_set(v___x_1104_, 9, v_maxHeartbeats_1096_);
lean_ctor_set(v___x_1104_, 10, v_quotContext_1097_);
lean_ctor_set(v___x_1104_, 11, v_currMacroScope_1098_);
lean_ctor_set(v___x_1104_, 12, v_cancelTk_x3f_1100_);
lean_ctor_set(v___x_1104_, 13, v_inheritedTraceOptions_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*14, v_diag_1099_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*14 + 1, v_suppressElabErrors_1101_);
lean_inc(v___y_1079_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1105_ = lean_apply_10(v_k_1071_, v_val_1081_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___x_1104_, v___y_1079_, lean_box(0));
return v___x_1105_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_k_1071_);
v___x_1106_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1107_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1070_, v___x_1106_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_stx_1070_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1108_, lean_object* v_k_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1108_, v_k_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1132_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1121_, v___x_1131_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1147_);
return v___x_1158_;
}
else
{
lean_object* v_a_1159_; lean_object* v_name_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_array_uget_borrowed(v_as_1144_, v_i_1146_);
v_name_1160_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_name_1160_);
v___x_1161_ = lean_mk_syntax_ident(v_name_1160_);
lean_inc(v___x_1161_);
v___x_1162_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1161_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1161_, v_a_1163_, v_b_1147_, v___y_1154_);
lean_dec(v_a_1163_);
lean_dec(v___x_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; size_t v___x_1166_; size_t v___x_1167_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1146_, v___x_1166_);
v_i_1146_ = v___x_1167_;
v_b_1147_ = v_a_1165_;
goto _start;
}
else
{
return v___x_1164_;
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v___x_1161_);
lean_dec_ref(v_b_1147_);
v_a_1169_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1162_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1162_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1177_, lean_object* v_sz_1178_, lean_object* v_i_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; lean_object* v_res_1192_; 
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1178_);
lean_dec(v_sz_1178_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1177_, v_sz_boxed_1190_, v_i_boxed_1191_, v_b_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_as_1177_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1212_, lean_object* v_stx_1213_, uint8_t v___x_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___f_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
if (v___x_1212_ == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_1228_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; lean_object* v_tk_1230_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1301_; uint8_t v___y_1302_; lean_object* v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; lean_object* v_stxForSuggestion_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; uint8_t v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; uint8_t v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; uint8_t v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; uint8_t v___y_1550_; lean_object* v___y_1563_; uint8_t v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v_stxForExecution_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; uint8_t v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1669_; uint8_t v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_argsArray_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; uint8_t v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1973_; uint8_t v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; uint8_t v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v_args_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___x_2026_; uint8_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v_o_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v_bang_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v_tk_1230_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_1229_);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2085_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_2026_);
v___x_2086_ = l_Lean_Syntax_isNone(v___x_2085_);
if (v___x_2086_ == 0)
{
uint8_t v___x_2087_; 
lean_inc(v___x_2085_);
v___x_2087_ = l_Lean_Syntax_matchesNull(v___x_2085_, v___x_2026_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec(v___x_2085_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2088_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2088_;
}
else
{
lean_object* v_bang_2089_; lean_object* v___x_2090_; 
v_bang_2089_ = l_Lean_Syntax_getArg(v___x_2085_, v___x_1229_);
lean_dec(v___x_2085_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_bang_2089_);
v_bang_2057_ = v___x_2090_;
v___y_2058_ = v___y_1219_;
v___y_2059_ = v___y_1220_;
v___y_2060_ = v___y_1221_;
v___y_2061_ = v___y_1222_;
v___y_2062_ = v___y_1223_;
v___y_2063_ = v___y_1224_;
v___y_2064_ = v___y_1225_;
v___y_2065_ = v___y_1226_;
goto v___jp_2056_;
}
}
else
{
lean_object* v___x_2091_; 
lean_dec(v___x_2085_);
v___x_2091_ = lean_box(0);
v_bang_2057_ = v___x_2091_;
v___y_2058_ = v___y_1219_;
v___y_2059_ = v___y_1220_;
v___y_2060_ = v___y_1221_;
v___y_2061_ = v___y_1222_;
v___y_2062_ = v___y_1223_;
v___y_2063_ = v___y_1224_;
v___y_2064_ = v___y_1225_;
v___y_2065_ = v___y_1226_;
goto v___jp_2056_;
}
v___jp_1231_:
{
lean_object* v___x_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(v___x_1214_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1246_, 0, v___y_1232_);
lean_closure_set(v___f_1246_, 1, v___x_1229_);
lean_closure_set(v___f_1246_, 2, v___x_1245_);
lean_closure_set(v___f_1246_, 3, v___y_1244_);
lean_closure_set(v___f_1246_, 4, v___y_1233_);
v___x_1247_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1234_, v___f_1246_, v___y_1236_, v___y_1242_, v___y_1240_, v___y_1238_, v___y_1241_, v___y_1237_, v___y_1243_, v___y_1235_);
lean_dec(v___y_1234_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v_usedTheorems_1249_; lean_object* v_diag_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1291_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v_usedTheorems_1249_ = lean_ctor_get(v_a_1248_, 0);
v_diag_1250_ = lean_ctor_get(v_a_1248_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1252_ = v_a_1248_;
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_diag_1250_);
lean_inc(v_usedTheorems_1249_);
lean_dec(v_a_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1239_, v_usedTheorems_1249_, v___y_1241_, v___y_1237_, v___y_1243_, v___y_1235_);
lean_dec_ref(v_usedTheorems_1249_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_ref_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v_ref_1256_ = lean_ctor_get(v___y_1243_, 5);
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_a_1255_);
lean_ctor_set(v___x_1252_, 0, v___x_1257_);
v___x_1259_ = v___x_1252_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1255_);
v___x_1259_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
lean_ctor_set(v___x_1261_, 3, v___x_1260_);
lean_ctor_set(v___x_1261_, 4, v___x_1260_);
lean_ctor_set(v___x_1261_, 5, v___x_1260_);
lean_inc(v_ref_1256_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_ref_1256_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1264_ = 4;
v___x_1265_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1230_, v___x_1261_, v___x_1262_, v___x_1263_, v___x_1260_, v___x_1264_, v___y_1243_, v___y_1235_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1265_, 0);
lean_dec(v_unused_1273_);
v___x_1267_ = v___x_1265_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_dec(v___x_1265_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_diag_1250_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_diag_1250_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v_diag_1250_);
v_a_1274_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1252_);
lean_dec_ref(v_diag_1250_);
lean_dec(v_tk_1230_);
v_a_1283_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1254_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1254_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v___y_1239_);
lean_dec(v_tk_1230_);
v_a_1292_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1247_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1247_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
v___jp_1300_:
{
uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = 0;
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1317_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1305_, v___x_1315_, v___y_1304_, v___x_1315_, v___x_1316_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1305_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref(v___x_1317_);
if (lean_obj_tag(v___y_1303_) == 0)
{
lean_object* v_ctx_1319_; lean_object* v_simprocs_1320_; lean_object* v_dischargeWrapper_1321_; 
v_ctx_1319_ = lean_ctor_get(v_a_1318_, 0);
lean_inc_ref(v_ctx_1319_);
v_simprocs_1320_ = lean_ctor_get(v_a_1318_, 1);
lean_inc_ref(v_simprocs_1320_);
v_dischargeWrapper_1321_ = lean_ctor_get(v_a_1318_, 2);
lean_inc(v_dischargeWrapper_1321_);
lean_dec(v_a_1318_);
v___y_1232_ = v___y_1301_;
v___y_1233_ = v_simprocs_1320_;
v___y_1234_ = v_dischargeWrapper_1321_;
v___y_1235_ = v___y_1314_;
v___y_1236_ = v___y_1307_;
v___y_1237_ = v___y_1312_;
v___y_1238_ = v___y_1310_;
v___y_1239_ = v_stxForSuggestion_1306_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1311_;
v___y_1242_ = v___y_1308_;
v___y_1243_ = v___y_1313_;
v___y_1244_ = v_ctx_1319_;
goto v___jp_1231_;
}
else
{
lean_dec_ref(v___y_1303_);
if (v___y_1302_ == 0)
{
lean_object* v_ctx_1322_; lean_object* v_simprocs_1323_; lean_object* v_dischargeWrapper_1324_; 
v_ctx_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc_ref(v_ctx_1322_);
v_simprocs_1323_ = lean_ctor_get(v_a_1318_, 1);
lean_inc_ref(v_simprocs_1323_);
v_dischargeWrapper_1324_ = lean_ctor_get(v_a_1318_, 2);
lean_inc(v_dischargeWrapper_1324_);
lean_dec(v_a_1318_);
v___y_1232_ = v___y_1301_;
v___y_1233_ = v_simprocs_1323_;
v___y_1234_ = v_dischargeWrapper_1324_;
v___y_1235_ = v___y_1314_;
v___y_1236_ = v___y_1307_;
v___y_1237_ = v___y_1312_;
v___y_1238_ = v___y_1310_;
v___y_1239_ = v_stxForSuggestion_1306_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1311_;
v___y_1242_ = v___y_1308_;
v___y_1243_ = v___y_1313_;
v___y_1244_ = v_ctx_1322_;
goto v___jp_1231_;
}
else
{
lean_object* v_ctx_1325_; lean_object* v_simprocs_1326_; lean_object* v_dischargeWrapper_1327_; lean_object* v___x_1328_; 
v_ctx_1325_ = lean_ctor_get(v_a_1318_, 0);
lean_inc_ref(v_ctx_1325_);
v_simprocs_1326_ = lean_ctor_get(v_a_1318_, 1);
lean_inc_ref(v_simprocs_1326_);
v_dischargeWrapper_1327_ = lean_ctor_get(v_a_1318_, 2);
lean_inc(v_dischargeWrapper_1327_);
lean_dec(v_a_1318_);
v___x_1328_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1325_);
v___y_1232_ = v___y_1301_;
v___y_1233_ = v_simprocs_1326_;
v___y_1234_ = v_dischargeWrapper_1327_;
v___y_1235_ = v___y_1314_;
v___y_1236_ = v___y_1307_;
v___y_1237_ = v___y_1312_;
v___y_1238_ = v___y_1310_;
v___y_1239_ = v_stxForSuggestion_1306_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1311_;
v___y_1242_ = v___y_1308_;
v___y_1243_ = v___y_1313_;
v___y_1244_ = v___x_1328_;
goto v___jp_1231_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_stxForSuggestion_1306_);
lean_dec(v___y_1303_);
lean_dec(v___y_1301_);
lean_dec(v_tk_1230_);
v_a_1329_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1317_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1317_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
v___jp_1337_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_inc_ref(v___y_1350_);
v___x_1361_ = l_Array_append___redArg(v___y_1350_, v___y_1360_);
lean_dec_ref(v___y_1360_);
lean_inc(v___y_1345_);
lean_inc(v___y_1340_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1340_);
lean_ctor_set(v___x_1362_, 1, v___y_1345_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = l_Lean_Syntax_node6(v___y_1340_, v___y_1343_, v___y_1358_, v___y_1341_, v___y_1348_, v___y_1349_, v___y_1359_, v___x_1362_);
v___y_1301_ = v___y_1338_;
v___y_1302_ = v___y_1342_;
v___y_1303_ = v___y_1352_;
v___y_1304_ = v___y_1355_;
v___y_1305_ = v___y_1354_;
v_stxForSuggestion_1306_ = v___x_1363_;
v___y_1307_ = v___y_1356_;
v___y_1308_ = v___y_1351_;
v___y_1309_ = v___y_1353_;
v___y_1310_ = v___y_1347_;
v___y_1311_ = v___y_1344_;
v___y_1312_ = v___y_1346_;
v___y_1313_ = v___y_1357_;
v___y_1314_ = v___y_1339_;
goto v___jp_1300_;
}
v___jp_1364_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref_n(v___y_1377_, 2);
v___x_1388_ = l_Array_append___redArg(v___y_1377_, v___y_1387_);
lean_dec_ref(v___y_1387_);
lean_inc_n(v___y_1371_, 3);
lean_inc_n(v___y_1366_, 5);
v___x_1389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1366_);
lean_ctor_set(v___x_1389_, 1, v___y_1371_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1366_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1393_ = l_Lean_Syntax_SepArray_ofElems(v___x_1392_, v___y_1375_);
lean_dec_ref(v___y_1375_);
v___x_1394_ = l_Array_append___redArg(v___y_1377_, v___x_1393_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1366_);
lean_ctor_set(v___x_1395_, 1, v___y_1371_);
lean_ctor_set(v___x_1395_, 2, v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1366_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l_Lean_Syntax_node3(v___y_1366_, v___y_1371_, v___x_1391_, v___x_1395_, v___x_1397_);
if (lean_obj_tag(v___y_1385_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1400_; 
v_val_1399_ = lean_ctor_get(v___y_1385_, 0);
lean_inc(v_val_1399_);
lean_dec_ref(v___y_1385_);
v___x_1400_ = l_Array_mkArray1___redArg(v_val_1399_);
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___y_1367_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1372_;
v___y_1345_ = v___y_1371_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___x_1389_;
v___y_1350_ = v___y_1377_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1383_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1381_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1386_;
v___y_1359_ = v___x_1398_;
v___y_1360_ = v___x_1400_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1401_; 
lean_dec(v___y_1385_);
v___x_1401_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___y_1367_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1372_;
v___y_1345_ = v___y_1371_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___x_1389_;
v___y_1350_ = v___y_1377_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1383_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1381_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1386_;
v___y_1359_ = v___x_1398_;
v___y_1360_ = v___x_1401_;
goto v___jp_1337_;
}
}
v___jp_1402_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_inc_ref(v___y_1414_);
v___x_1426_ = l_Array_append___redArg(v___y_1414_, v___y_1425_);
lean_dec_ref(v___y_1425_);
lean_inc(v___y_1409_);
lean_inc(v___y_1404_);
v___x_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1404_);
lean_ctor_set(v___x_1427_, 1, v___y_1409_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
if (lean_obj_tag(v___y_1418_) == 1)
{
lean_object* v_val_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_val_1428_ = lean_ctor_get(v___y_1418_, 0);
lean_inc(v_val_1428_);
lean_dec_ref(v___y_1418_);
v___x_1429_ = l_Lean_SourceInfo_fromRef(v_val_1428_, v___x_1214_);
lean_dec(v_val_1428_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = l_Array_mkArray1___redArg(v___x_1431_);
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___x_1427_;
v___y_1377_ = v___y_1414_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1417_;
v___y_1381_ = v___y_1421_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1419_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1423_;
v___y_1387_ = v___x_1432_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v___y_1418_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1413_;
v___y_1376_ = v___x_1427_;
v___y_1377_ = v___y_1414_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1417_;
v___y_1381_ = v___y_1421_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1419_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1423_;
v___y_1387_ = v___x_1433_;
goto v___jp_1364_;
}
}
v___jp_1434_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc_ref(v___y_1437_);
v___x_1458_ = l_Array_append___redArg(v___y_1437_, v___y_1457_);
lean_dec_ref(v___y_1457_);
lean_inc(v___y_1453_);
lean_inc(v___y_1444_);
v___x_1459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1459_, 0, v___y_1444_);
lean_ctor_set(v___x_1459_, 1, v___y_1453_);
lean_ctor_set(v___x_1459_, 2, v___x_1458_);
v___x_1460_ = l_Lean_Syntax_node6(v___y_1444_, v___y_1450_, v___y_1456_, v___y_1438_, v___y_1439_, v___y_1442_, v___y_1449_, v___x_1459_);
v___y_1301_ = v___y_1435_;
v___y_1302_ = v___y_1440_;
v___y_1303_ = v___y_1447_;
v___y_1304_ = v___y_1452_;
v___y_1305_ = v___y_1451_;
v_stxForSuggestion_1306_ = v___x_1460_;
v___y_1307_ = v___y_1454_;
v___y_1308_ = v___y_1446_;
v___y_1309_ = v___y_1448_;
v___y_1310_ = v___y_1445_;
v___y_1311_ = v___y_1441_;
v___y_1312_ = v___y_1443_;
v___y_1313_ = v___y_1455_;
v___y_1314_ = v___y_1436_;
goto v___jp_1300_;
}
v___jp_1461_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_inc_ref_n(v___y_1463_, 2);
v___x_1485_ = l_Array_append___redArg(v___y_1463_, v___y_1484_);
lean_dec_ref(v___y_1484_);
lean_inc_n(v___y_1480_, 3);
lean_inc_n(v___y_1469_, 5);
v___x_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1469_);
lean_ctor_set(v___x_1486_, 1, v___y_1480_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1469_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1490_ = l_Lean_Syntax_SepArray_ofElems(v___x_1489_, v___y_1472_);
lean_dec_ref(v___y_1472_);
v___x_1491_ = l_Array_append___redArg(v___y_1463_, v___x_1490_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1469_);
lean_ctor_set(v___x_1492_, 1, v___y_1480_);
lean_ctor_set(v___x_1492_, 2, v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1469_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_Syntax_node3(v___y_1469_, v___y_1480_, v___x_1488_, v___x_1492_, v___x_1494_);
if (lean_obj_tag(v___y_1482_) == 1)
{
lean_object* v_val_1496_; lean_object* v___x_1497_; 
v_val_1496_ = lean_ctor_get(v___y_1482_, 0);
lean_inc(v_val_1496_);
lean_dec_ref(v___y_1482_);
v___x_1497_ = l_Array_mkArray1___redArg(v_val_1496_);
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1464_;
v___y_1437_ = v___y_1463_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___x_1486_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1471_;
v___y_1446_ = v___y_1473_;
v___y_1447_ = v___y_1474_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___x_1495_;
v___y_1450_ = v___y_1476_;
v___y_1451_ = v___y_1479_;
v___y_1452_ = v___y_1478_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1477_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___x_1497_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1498_; 
lean_dec(v___y_1482_);
v___x_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1464_;
v___y_1437_ = v___y_1463_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___x_1486_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1471_;
v___y_1446_ = v___y_1473_;
v___y_1447_ = v___y_1474_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___x_1495_;
v___y_1450_ = v___y_1476_;
v___y_1451_ = v___y_1479_;
v___y_1452_ = v___y_1478_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1477_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___x_1498_;
goto v___jp_1434_;
}
}
v___jp_1499_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_inc_ref(v___y_1501_);
v___x_1523_ = l_Array_append___redArg(v___y_1501_, v___y_1522_);
lean_dec_ref(v___y_1522_);
lean_inc(v___y_1518_);
lean_inc(v___y_1506_);
v___x_1524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1506_);
lean_ctor_set(v___x_1524_, 1, v___y_1518_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
if (lean_obj_tag(v___y_1514_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_val_1525_ = lean_ctor_get(v___y_1514_, 0);
lean_inc(v_val_1525_);
lean_dec_ref(v___y_1514_);
v___x_1526_ = l_Lean_SourceInfo_fromRef(v_val_1525_, v___x_1214_);
lean_dec(v_val_1525_);
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Array_mkArray1___redArg(v___x_1528_);
v___y_1462_ = v___y_1500_;
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___x_1524_;
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
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1515_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1521_;
v___y_1483_ = v___y_1520_;
v___y_1484_ = v___x_1529_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1530_; 
lean_dec(v___y_1514_);
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1462_ = v___y_1500_;
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___x_1524_;
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
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1515_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1521_;
v___y_1483_ = v___y_1520_;
v___y_1484_ = v___x_1530_;
goto v___jp_1461_;
}
}
v___jp_1531_:
{
lean_object* v_ref_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_ref_1551_ = lean_ctor_get(v___y_1548_, 5);
v___x_1552_ = l_Lean_SourceInfo_fromRef(v_ref_1551_, v___y_1550_);
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1554_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1553_);
v___x_1555_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1553_);
v___x_1557_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1558_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1536_) == 1)
{
lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_val_1559_ = lean_ctor_get(v___y_1536_, 0);
lean_inc(v_val_1559_);
lean_dec_ref(v___y_1536_);
v___x_1560_ = l_Array_mkArray1___redArg(v_val_1559_);
v___y_1500_ = v___y_1532_;
v___y_1501_ = v___x_1558_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1537_;
v___y_1506_ = v___x_1552_;
v___y_1507_ = v___y_1538_;
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v___x_1554_;
v___y_1514_ = v___y_1547_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1544_;
v___y_1518_ = v___x_1557_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___x_1556_;
v___y_1521_ = v___y_1549_;
v___y_1522_ = v___x_1560_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1561_; 
lean_dec(v___y_1536_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1500_ = v___y_1532_;
v___y_1501_ = v___x_1558_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1537_;
v___y_1506_ = v___x_1552_;
v___y_1507_ = v___y_1538_;
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v___x_1554_;
v___y_1514_ = v___y_1547_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1544_;
v___y_1518_ = v___x_1557_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___x_1556_;
v___y_1521_ = v___y_1549_;
v___y_1522_ = v___x_1561_;
goto v___jp_1499_;
}
}
v___jp_1562_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1571_);
if (lean_obj_tag(v___y_1565_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1581_);
v___x_1583_ = 0;
v___y_1532_ = v___y_1563_;
v___y_1533_ = v___y_1580_;
v___y_1534_ = v_a_1582_;
v___y_1535_ = v___y_1564_;
v___y_1536_ = v___y_1566_;
v___y_1537_ = v___y_1577_;
v___y_1538_ = v___y_1578_;
v___y_1539_ = v___y_1576_;
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1574_;
v___y_1542_ = v___y_1565_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1568_;
v___y_1546_ = v_stxForExecution_1572_;
v___y_1547_ = v___y_1567_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1570_;
v___y_1550_ = v___x_1583_;
goto v___jp_1531_;
}
else
{
if (v___y_1564_ == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1581_);
v___y_1532_ = v___y_1563_;
v___y_1533_ = v___y_1580_;
v___y_1534_ = v_a_1584_;
v___y_1535_ = v___y_1564_;
v___y_1536_ = v___y_1566_;
v___y_1537_ = v___y_1577_;
v___y_1538_ = v___y_1578_;
v___y_1539_ = v___y_1576_;
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1574_;
v___y_1542_ = v___y_1565_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1568_;
v___y_1546_ = v_stxForExecution_1572_;
v___y_1547_ = v___y_1567_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1570_;
v___y_1550_ = v___y_1564_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1585_; lean_object* v_ref_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1585_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1581_);
v_ref_1586_ = lean_ctor_get(v___y_1579_, 5);
v___x_1587_ = 0;
v___x_1588_ = l_Lean_SourceInfo_fromRef(v_ref_1586_, v___x_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1590_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1589_);
v___x_1591_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1595_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1566_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1597_; 
v_val_1596_ = lean_ctor_get(v___y_1566_, 0);
lean_inc(v_val_1596_);
lean_dec_ref(v___y_1566_);
v___x_1597_ = l_Array_mkArray1___redArg(v_val_1596_);
v___y_1403_ = v___y_1563_;
v___y_1404_ = v___x_1588_;
v___y_1405_ = v___y_1580_;
v___y_1406_ = v_a_1585_;
v___y_1407_ = v___y_1564_;
v___y_1408_ = v___x_1590_;
v___y_1409_ = v___x_1594_;
v___y_1410_ = v___y_1577_;
v___y_1411_ = v___y_1578_;
v___y_1412_ = v___y_1576_;
v___y_1413_ = v___y_1569_;
v___y_1414_ = v___x_1595_;
v___y_1415_ = v___y_1574_;
v___y_1416_ = v___y_1565_;
v___y_1417_ = v___y_1575_;
v___y_1418_ = v___y_1567_;
v___y_1419_ = v_stxForExecution_1572_;
v___y_1420_ = v___y_1568_;
v___y_1421_ = v___y_1573_;
v___y_1422_ = v___y_1579_;
v___y_1423_ = v___x_1593_;
v___y_1424_ = v___y_1570_;
v___y_1425_ = v___x_1597_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1598_; 
lean_dec(v___y_1566_);
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1403_ = v___y_1563_;
v___y_1404_ = v___x_1588_;
v___y_1405_ = v___y_1580_;
v___y_1406_ = v_a_1585_;
v___y_1407_ = v___y_1564_;
v___y_1408_ = v___x_1590_;
v___y_1409_ = v___x_1594_;
v___y_1410_ = v___y_1577_;
v___y_1411_ = v___y_1578_;
v___y_1412_ = v___y_1576_;
v___y_1413_ = v___y_1569_;
v___y_1414_ = v___x_1595_;
v___y_1415_ = v___y_1574_;
v___y_1416_ = v___y_1565_;
v___y_1417_ = v___y_1575_;
v___y_1418_ = v___y_1567_;
v___y_1419_ = v_stxForExecution_1572_;
v___y_1420_ = v___y_1568_;
v___y_1421_ = v___y_1573_;
v___y_1422_ = v___y_1579_;
v___y_1423_ = v___x_1593_;
v___y_1424_ = v___y_1570_;
v___y_1425_ = v___x_1598_;
goto v___jp_1402_;
}
}
}
}
v___jp_1599_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_inc_ref(v___y_1609_);
v___x_1626_ = l_Array_append___redArg(v___y_1609_, v___y_1625_);
lean_dec_ref(v___y_1625_);
lean_inc(v___y_1605_);
lean_inc(v___y_1607_);
v___x_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1607_);
lean_ctor_set(v___x_1627_, 1, v___y_1605_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
lean_inc(v___y_1624_);
v___x_1628_ = l_Lean_Syntax_node6(v___y_1607_, v___y_1614_, v___y_1606_, v___y_1624_, v___y_1604_, v___y_1618_, v___y_1615_, v___x_1627_);
v___y_1563_ = v___y_1600_;
v___y_1564_ = v___y_1613_;
v___y_1565_ = v___y_1619_;
v___y_1566_ = v___y_1601_;
v___y_1567_ = v___y_1621_;
v___y_1568_ = v___y_1608_;
v___y_1569_ = v___y_1617_;
v___y_1570_ = v___y_1612_;
v___y_1571_ = v___y_1624_;
v_stxForExecution_1572_ = v___x_1628_;
v___y_1573_ = v___y_1620_;
v___y_1574_ = v___y_1603_;
v___y_1575_ = v___y_1622_;
v___y_1576_ = v___y_1616_;
v___y_1577_ = v___y_1610_;
v___y_1578_ = v___y_1602_;
v___y_1579_ = v___y_1623_;
v___y_1580_ = v___y_1611_;
goto v___jp_1562_;
}
v___jp_1629_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_inc_ref_n(v___y_1647_, 2);
v___x_1654_ = l_Array_append___redArg(v___y_1647_, v___y_1653_);
lean_dec_ref(v___y_1653_);
lean_inc_n(v___y_1640_, 3);
lean_inc_n(v___y_1643_, 5);
v___x_1655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1643_);
lean_ctor_set(v___x_1655_, 1, v___y_1640_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___y_1643_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1659_ = l_Lean_Syntax_SepArray_ofElems(v___x_1658_, v___y_1636_);
v___x_1660_ = l_Array_append___redArg(v___y_1647_, v___x_1659_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1643_);
lean_ctor_set(v___x_1661_, 1, v___y_1640_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1643_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node3(v___y_1643_, v___y_1640_, v___x_1657_, v___x_1661_, v___x_1663_);
if (lean_obj_tag(v___y_1649_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1666_; 
v_val_1665_ = lean_ctor_get(v___y_1649_, 0);
lean_inc(v_val_1665_);
v___x_1666_ = l_Array_mkArray1___redArg(v_val_1665_);
v___y_1600_ = v___y_1630_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1635_;
v___y_1603_ = v___y_1637_;
v___y_1604_ = v___y_1638_;
v___y_1605_ = v___y_1640_;
v___y_1606_ = v___y_1642_;
v___y_1607_ = v___y_1643_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___y_1647_;
v___y_1610_ = v___y_1650_;
v___y_1611_ = v___y_1651_;
v___y_1612_ = v___y_1649_;
v___y_1613_ = v___y_1631_;
v___y_1614_ = v___y_1632_;
v___y_1615_ = v___x_1664_;
v___y_1616_ = v___y_1634_;
v___y_1617_ = v___y_1636_;
v___y_1618_ = v___x_1655_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1641_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v___y_1646_;
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1652_;
v___y_1625_ = v___x_1666_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1600_ = v___y_1630_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1635_;
v___y_1603_ = v___y_1637_;
v___y_1604_ = v___y_1638_;
v___y_1605_ = v___y_1640_;
v___y_1606_ = v___y_1642_;
v___y_1607_ = v___y_1643_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___y_1647_;
v___y_1610_ = v___y_1650_;
v___y_1611_ = v___y_1651_;
v___y_1612_ = v___y_1649_;
v___y_1613_ = v___y_1631_;
v___y_1614_ = v___y_1632_;
v___y_1615_ = v___x_1664_;
v___y_1616_ = v___y_1634_;
v___y_1617_ = v___y_1636_;
v___y_1618_ = v___x_1655_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1641_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v___y_1646_;
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1652_;
v___y_1625_ = v___x_1667_;
goto v___jp_1599_;
}
}
v___jp_1668_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_inc_ref(v___y_1685_);
v___x_1692_ = l_Array_append___redArg(v___y_1685_, v___y_1691_);
lean_dec_ref(v___y_1691_);
lean_inc(v___y_1677_);
lean_inc(v___y_1681_);
v___x_1693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1681_);
lean_ctor_set(v___x_1693_, 1, v___y_1677_);
lean_ctor_set(v___x_1693_, 2, v___x_1692_);
if (lean_obj_tag(v___y_1683_) == 1)
{
lean_object* v_val_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_val_1694_ = lean_ctor_get(v___y_1683_, 0);
v___x_1695_ = l_Lean_SourceInfo_fromRef(v_val_1694_, v___x_1214_);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Array_mkArray1___redArg(v___x_1697_);
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___x_1693_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1677_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___y_1681_;
v___y_1644_ = v___y_1683_;
v___y_1645_ = v___y_1682_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1689_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1687_;
v___y_1651_ = v___y_1686_;
v___y_1652_ = v___y_1690_;
v___y_1653_ = v___x_1698_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___x_1693_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1677_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1680_;
v___y_1643_ = v___y_1681_;
v___y_1644_ = v___y_1683_;
v___y_1645_ = v___y_1682_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1689_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1687_;
v___y_1651_ = v___y_1686_;
v___y_1652_ = v___y_1690_;
v___y_1653_ = v___x_1699_;
goto v___jp_1629_;
}
}
v___jp_1700_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_inc_ref(v___y_1713_);
v___x_1727_ = l_Array_append___redArg(v___y_1713_, v___y_1726_);
lean_dec_ref(v___y_1726_);
lean_inc(v___y_1723_);
lean_inc(v___y_1707_);
v___x_1728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1728_, 0, v___y_1707_);
lean_ctor_set(v___x_1728_, 1, v___y_1723_);
lean_ctor_set(v___x_1728_, 2, v___x_1727_);
lean_inc(v___y_1725_);
v___x_1729_ = l_Lean_Syntax_node6(v___y_1707_, v___y_1704_, v___y_1714_, v___y_1725_, v___y_1702_, v___y_1716_, v___y_1708_, v___x_1728_);
v___y_1563_ = v___y_1701_;
v___y_1564_ = v___y_1715_;
v___y_1565_ = v___y_1719_;
v___y_1566_ = v___y_1703_;
v___y_1567_ = v___y_1721_;
v___y_1568_ = v___y_1709_;
v___y_1569_ = v___y_1718_;
v___y_1570_ = v___y_1712_;
v___y_1571_ = v___y_1725_;
v_stxForExecution_1572_ = v___x_1729_;
v___y_1573_ = v___y_1720_;
v___y_1574_ = v___y_1706_;
v___y_1575_ = v___y_1722_;
v___y_1576_ = v___y_1717_;
v___y_1577_ = v___y_1710_;
v___y_1578_ = v___y_1705_;
v___y_1579_ = v___y_1724_;
v___y_1580_ = v___y_1711_;
goto v___jp_1562_;
}
v___jp_1730_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_inc_ref_n(v___y_1732_, 2);
v___x_1755_ = l_Array_append___redArg(v___y_1732_, v___y_1754_);
lean_dec_ref(v___y_1754_);
lean_inc_n(v___y_1750_, 3);
lean_inc_n(v___y_1742_, 5);
v___x_1756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1742_);
lean_ctor_set(v___x_1756_, 1, v___y_1750_);
lean_ctor_set(v___x_1756_, 2, v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1742_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1760_ = l_Lean_Syntax_SepArray_ofElems(v___x_1759_, v___y_1740_);
v___x_1761_ = l_Array_append___redArg(v___y_1732_, v___x_1760_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1762_, 0, v___y_1742_);
lean_ctor_set(v___x_1762_, 1, v___y_1750_);
lean_ctor_set(v___x_1762_, 2, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___y_1742_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node3(v___y_1742_, v___y_1750_, v___x_1758_, v___x_1762_, v___x_1764_);
if (lean_obj_tag(v___y_1749_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1767_; 
v_val_1766_ = lean_ctor_get(v___y_1749_, 0);
lean_inc(v_val_1766_);
v___x_1767_ = l_Array_mkArray1___redArg(v_val_1766_);
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1735_;
v___y_1703_ = v___y_1736_;
v___y_1704_ = v___y_1737_;
v___y_1705_ = v___y_1739_;
v___y_1706_ = v___y_1741_;
v___y_1707_ = v___y_1742_;
v___y_1708_ = v___x_1765_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1751_;
v___y_1711_ = v___y_1752_;
v___y_1712_ = v___y_1749_;
v___y_1713_ = v___y_1732_;
v___y_1714_ = v___y_1734_;
v___y_1715_ = v___y_1733_;
v___y_1716_ = v___x_1756_;
v___y_1717_ = v___y_1738_;
v___y_1718_ = v___y_1740_;
v___y_1719_ = v___y_1743_;
v___y_1720_ = v___y_1744_;
v___y_1721_ = v___y_1745_;
v___y_1722_ = v___y_1747_;
v___y_1723_ = v___y_1750_;
v___y_1724_ = v___y_1748_;
v___y_1725_ = v___y_1753_;
v___y_1726_ = v___x_1767_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1735_;
v___y_1703_ = v___y_1736_;
v___y_1704_ = v___y_1737_;
v___y_1705_ = v___y_1739_;
v___y_1706_ = v___y_1741_;
v___y_1707_ = v___y_1742_;
v___y_1708_ = v___x_1765_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1751_;
v___y_1711_ = v___y_1752_;
v___y_1712_ = v___y_1749_;
v___y_1713_ = v___y_1732_;
v___y_1714_ = v___y_1734_;
v___y_1715_ = v___y_1733_;
v___y_1716_ = v___x_1756_;
v___y_1717_ = v___y_1738_;
v___y_1718_ = v___y_1740_;
v___y_1719_ = v___y_1743_;
v___y_1720_ = v___y_1744_;
v___y_1721_ = v___y_1745_;
v___y_1722_ = v___y_1747_;
v___y_1723_ = v___y_1750_;
v___y_1724_ = v___y_1748_;
v___y_1725_ = v___y_1753_;
v___y_1726_ = v___x_1768_;
goto v___jp_1700_;
}
}
v___jp_1769_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_inc_ref(v___y_1771_);
v___x_1793_ = l_Array_append___redArg(v___y_1771_, v___y_1792_);
lean_dec_ref(v___y_1792_);
lean_inc(v___y_1790_);
lean_inc(v___y_1780_);
v___x_1794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1794_, 0, v___y_1780_);
lean_ctor_set(v___x_1794_, 1, v___y_1790_);
lean_ctor_set(v___x_1794_, 2, v___x_1793_);
if (lean_obj_tag(v___y_1784_) == 1)
{
lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_val_1795_ = lean_ctor_get(v___y_1784_, 0);
v___x_1796_ = l_Lean_SourceInfo_fromRef(v_val_1795_, v___x_1214_);
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = l_Array_mkArray1___redArg(v___x_1798_);
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___x_1794_;
v___y_1736_ = v___y_1774_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___y_1777_;
v___y_1740_ = v___y_1778_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1780_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___y_1782_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1783_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v___y_1789_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1790_;
v___y_1751_ = v___y_1787_;
v___y_1752_ = v___y_1786_;
v___y_1753_ = v___y_1791_;
v___y_1754_ = v___x_1799_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___x_1794_;
v___y_1736_ = v___y_1774_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___y_1777_;
v___y_1740_ = v___y_1778_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1780_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___y_1782_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1783_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v___y_1789_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1790_;
v___y_1751_ = v___y_1787_;
v___y_1752_ = v___y_1786_;
v___y_1753_ = v___y_1791_;
v___y_1754_ = v___x_1800_;
goto v___jp_1730_;
}
}
v___jp_1801_:
{
lean_object* v_ref_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_ref_1820_ = lean_ctor_get(v___y_1817_, 5);
v___x_1821_ = l_Lean_SourceInfo_fromRef(v_ref_1820_, v___y_1819_);
v___x_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_1823_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1822_);
v___x_1824_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1822_);
v___x_1826_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1827_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1804_) == 1)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; 
v_val_1828_ = lean_ctor_get(v___y_1804_, 0);
lean_inc(v_val_1828_);
v___x_1829_ = l_Array_mkArray1___redArg(v_val_1828_);
v___y_1770_ = v___y_1802_;
v___y_1771_ = v___x_1827_;
v___y_1772_ = v___y_1803_;
v___y_1773_ = v___x_1825_;
v___y_1774_ = v___y_1804_;
v___y_1775_ = v___x_1823_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v___y_1806_;
v___y_1778_ = v___y_1807_;
v___y_1779_ = v___y_1808_;
v___y_1780_ = v___x_1821_;
v___y_1781_ = v___y_1809_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1813_;
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1814_;
v___y_1789_ = v___y_1817_;
v___y_1790_ = v___x_1826_;
v___y_1791_ = v___y_1818_;
v___y_1792_ = v___x_1829_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1770_ = v___y_1802_;
v___y_1771_ = v___x_1827_;
v___y_1772_ = v___y_1803_;
v___y_1773_ = v___x_1825_;
v___y_1774_ = v___y_1804_;
v___y_1775_ = v___x_1823_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v___y_1806_;
v___y_1778_ = v___y_1807_;
v___y_1779_ = v___y_1808_;
v___y_1780_ = v___x_1821_;
v___y_1781_ = v___y_1809_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1813_;
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1814_;
v___y_1789_ = v___y_1817_;
v___y_1790_ = v___x_1826_;
v___y_1791_ = v___y_1818_;
v___y_1792_ = v___x_1830_;
goto v___jp_1769_;
}
}
v___jp_1831_:
{
if (lean_obj_tag(v___y_1834_) == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = 0;
v___y_1802_ = v___y_1832_;
v___y_1803_ = v___y_1833_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v___y_1844_;
v___y_1806_ = v___y_1846_;
v___y_1807_ = v_argsArray_1840_;
v___y_1808_ = v___y_1842_;
v___y_1809_ = v___y_1834_;
v___y_1810_ = v___y_1841_;
v___y_1811_ = v___y_1836_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1843_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1848_;
v___y_1817_ = v___y_1847_;
v___y_1818_ = v___y_1839_;
v___y_1819_ = v___x_1849_;
goto v___jp_1801_;
}
else
{
if (v___y_1833_ == 0)
{
v___y_1802_ = v___y_1832_;
v___y_1803_ = v___y_1833_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v___y_1844_;
v___y_1806_ = v___y_1846_;
v___y_1807_ = v_argsArray_1840_;
v___y_1808_ = v___y_1842_;
v___y_1809_ = v___y_1834_;
v___y_1810_ = v___y_1841_;
v___y_1811_ = v___y_1836_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1843_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1848_;
v___y_1817_ = v___y_1847_;
v___y_1818_ = v___y_1839_;
v___y_1819_ = v___y_1833_;
goto v___jp_1801_;
}
else
{
lean_object* v_ref_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_ref_1850_ = lean_ctor_get(v___y_1847_, 5);
v___x_1851_ = 0;
v___x_1852_ = l_Lean_SourceInfo_fromRef(v_ref_1850_, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_1854_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1853_);
v___x_1855_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1859_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1835_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1861_; 
v_val_1860_ = lean_ctor_get(v___y_1835_, 0);
lean_inc(v_val_1860_);
v___x_1861_ = l_Array_mkArray1___redArg(v_val_1860_);
v___y_1669_ = v___y_1832_;
v___y_1670_ = v___y_1833_;
v___y_1671_ = v___x_1854_;
v___y_1672_ = v___y_1835_;
v___y_1673_ = v___y_1844_;
v___y_1674_ = v___y_1846_;
v___y_1675_ = v_argsArray_1840_;
v___y_1676_ = v___y_1842_;
v___y_1677_ = v___x_1858_;
v___y_1678_ = v___y_1834_;
v___y_1679_ = v___y_1841_;
v___y_1680_ = v___x_1857_;
v___y_1681_ = v___x_1852_;
v___y_1682_ = v___y_1836_;
v___y_1683_ = v___y_1837_;
v___y_1684_ = v___y_1843_;
v___y_1685_ = v___x_1859_;
v___y_1686_ = v___y_1848_;
v___y_1687_ = v___y_1845_;
v___y_1688_ = v___y_1838_;
v___y_1689_ = v___y_1847_;
v___y_1690_ = v___y_1839_;
v___y_1691_ = v___x_1861_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1669_ = v___y_1832_;
v___y_1670_ = v___y_1833_;
v___y_1671_ = v___x_1854_;
v___y_1672_ = v___y_1835_;
v___y_1673_ = v___y_1844_;
v___y_1674_ = v___y_1846_;
v___y_1675_ = v_argsArray_1840_;
v___y_1676_ = v___y_1842_;
v___y_1677_ = v___x_1858_;
v___y_1678_ = v___y_1834_;
v___y_1679_ = v___y_1841_;
v___y_1680_ = v___x_1857_;
v___y_1681_ = v___x_1852_;
v___y_1682_ = v___y_1836_;
v___y_1683_ = v___y_1837_;
v___y_1684_ = v___y_1843_;
v___y_1685_ = v___x_1859_;
v___y_1686_ = v___y_1848_;
v___y_1687_ = v___y_1845_;
v___y_1688_ = v___y_1838_;
v___y_1689_ = v___y_1847_;
v___y_1690_ = v___y_1839_;
v___y_1691_ = v___x_1862_;
goto v___jp_1668_;
}
}
}
}
v___jp_1863_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1873_, v___y_1874_, v___y_1869_, v___y_1871_, v___y_1865_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_LibrarySuggestions_select(v_a_1883_, v___y_1881_, v___y_1874_, v___y_1869_, v___y_1871_, v___y_1865_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; size_t v_sz_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v_sz_1886_ = lean_array_size(v_a_1885_);
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1885_, v_sz_1886_, v___x_1887_, v___y_1879_, v___y_1868_, v___y_1873_, v___y_1877_, v___y_1870_, v___y_1874_, v___y_1869_, v___y_1871_, v___y_1865_);
lean_dec(v_a_1885_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1866_;
v___y_1834_ = v___y_1872_;
v___y_1835_ = v___y_1867_;
v___y_1836_ = v___y_1876_;
v___y_1837_ = v___y_1875_;
v___y_1838_ = v___y_1878_;
v___y_1839_ = v___y_1880_;
v_argsArray_1840_ = v_a_1889_;
v___y_1841_ = v___y_1868_;
v___y_1842_ = v___y_1873_;
v___y_1843_ = v___y_1877_;
v___y_1844_ = v___y_1870_;
v___y_1845_ = v___y_1874_;
v___y_1846_ = v___y_1869_;
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1865_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v___y_1880_);
lean_dec(v___y_1878_);
lean_dec(v___y_1875_);
lean_dec(v___y_1872_);
lean_dec(v___y_1867_);
lean_dec(v___y_1864_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1890_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1888_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1888_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1875_);
lean_dec(v___y_1872_);
lean_dec(v___y_1867_);
lean_dec(v___y_1864_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1898_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1884_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1884_);
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
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1875_);
lean_dec(v___y_1872_);
lean_dec(v___y_1867_);
lean_dec(v___y_1864_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1906_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1882_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1882_);
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
uint8_t v_suggestions_1933_; 
v_suggestions_1933_ = lean_ctor_get_uint8(v___y_1919_, sizeof(void*)*3 + 26);
if (v_suggestions_1933_ == 0)
{
lean_dec_ref(v___y_1919_);
lean_dec_ref(v___f_1218_);
v___y_1832_ = v___y_1915_;
v___y_1833_ = v___y_1917_;
v___y_1834_ = v___y_1924_;
v___y_1835_ = v___y_1918_;
v___y_1836_ = v___y_1929_;
v___y_1837_ = v___y_1928_;
v___y_1838_ = v___y_1930_;
v___y_1839_ = v___y_1931_;
v_argsArray_1840_ = v___y_1932_;
v___y_1841_ = v___y_1920_;
v___y_1842_ = v___y_1925_;
v___y_1843_ = v___y_1927_;
v___y_1844_ = v___y_1922_;
v___y_1845_ = v___y_1926_;
v___y_1846_ = v___y_1921_;
v___y_1847_ = v___y_1923_;
v___y_1848_ = v___y_1916_;
goto v___jp_1831_;
}
else
{
lean_object* v_maxSuggestions_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_maxSuggestions_1934_ = lean_ctor_get(v___y_1919_, 2);
lean_inc(v_maxSuggestions_1934_);
lean_dec_ref(v___y_1919_);
v___x_1935_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1936_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1934_) == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_unsigned_to_nat(100u);
v___x_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1935_);
lean_ctor_set(v___x_1938_, 2, v___f_1218_);
lean_ctor_set(v___x_1938_, 3, v___x_1936_);
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1920_;
v___y_1869_ = v___y_1921_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1924_;
v___y_1873_ = v___y_1925_;
v___y_1874_ = v___y_1926_;
v___y_1875_ = v___y_1928_;
v___y_1876_ = v___y_1929_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1930_;
v___y_1879_ = v___y_1932_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___x_1938_;
goto v___jp_1863_;
}
else
{
lean_object* v_val_1939_; lean_object* v___x_1940_; 
v_val_1939_ = lean_ctor_get(v_maxSuggestions_1934_, 0);
lean_inc(v_val_1939_);
lean_dec_ref(v_maxSuggestions_1934_);
v___x_1940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1940_, 0, v_val_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1935_);
lean_ctor_set(v___x_1940_, 2, v___f_1218_);
lean_ctor_set(v___x_1940_, 3, v___x_1936_);
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1920_;
v___y_1869_ = v___y_1921_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1924_;
v___y_1873_ = v___y_1925_;
v___y_1874_ = v___y_1926_;
v___y_1875_ = v___y_1928_;
v___y_1876_ = v___y_1929_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1930_;
v___y_1879_ = v___y_1932_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___x_1940_;
goto v___jp_1863_;
}
}
}
v___jp_1941_:
{
uint8_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = 0;
lean_inc(v___y_1942_);
v___x_1958_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1942_, v___x_1957_, v___y_1943_, v___y_1954_, v___y_1948_, v___y_1946_, v___y_1947_, v___y_1955_, v___y_1944_);
if (lean_obj_tag(v___x_1958_) == 0)
{
if (lean_obj_tag(v___y_1950_) == 1)
{
lean_object* v_a_1959_; lean_object* v_val_1960_; lean_object* v___x_1961_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___x_1958_);
v_val_1960_ = lean_ctor_get(v___y_1950_, 0);
lean_inc(v_val_1960_);
lean_dec_ref(v___y_1950_);
v___x_1961_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1960_);
lean_dec(v_val_1960_);
lean_inc(v___y_1945_);
v___y_1915_ = v___y_1945_;
v___y_1916_ = v___y_1944_;
v___y_1917_ = v___y_1953_;
v___y_1918_ = v___y_1956_;
v___y_1919_ = v_a_1959_;
v___y_1920_ = v___y_1943_;
v___y_1921_ = v___y_1947_;
v___y_1922_ = v___y_1948_;
v___y_1923_ = v___y_1955_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1952_;
v___y_1926_ = v___y_1946_;
v___y_1927_ = v___y_1954_;
v___y_1928_ = v___y_1951_;
v___y_1929_ = v___x_1957_;
v___y_1930_ = v___y_1945_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___x_1961_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
lean_dec(v___y_1950_);
v_a_1962_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1958_);
v___x_1963_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1945_);
v___y_1915_ = v___y_1945_;
v___y_1916_ = v___y_1944_;
v___y_1917_ = v___y_1953_;
v___y_1918_ = v___y_1956_;
v___y_1919_ = v_a_1962_;
v___y_1920_ = v___y_1943_;
v___y_1921_ = v___y_1947_;
v___y_1922_ = v___y_1948_;
v___y_1923_ = v___y_1955_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1952_;
v___y_1926_ = v___y_1946_;
v___y_1927_ = v___y_1954_;
v___y_1928_ = v___y_1951_;
v___y_1929_ = v___x_1957_;
v___y_1930_ = v___y_1945_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___x_1963_;
goto v___jp_1914_;
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v___y_1956_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec(v___y_1945_);
lean_dec(v___y_1942_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1964_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1958_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1958_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
v___jp_1972_:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Syntax_getOptional_x3f(v___y_1975_);
lean_dec(v___y_1975_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_box(0);
v___y_1942_ = v___y_1986_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1973_;
v___y_1945_ = v___y_1987_;
v___y_1946_ = v___y_1982_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1983_;
v___y_1951_ = v___y_1984_;
v___y_1952_ = v___y_1981_;
v___y_1953_ = v___y_1974_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___y_1979_;
v___y_1956_ = v___x_1989_;
goto v___jp_1941_;
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1988_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v___x_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_val_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v___y_1942_ = v___y_1986_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1973_;
v___y_1945_ = v___y_1987_;
v___y_1946_ = v___y_1982_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1983_;
v___y_1951_ = v___y_1984_;
v___y_1952_ = v___y_1981_;
v___y_1953_ = v___y_1974_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___y_1979_;
v___y_1956_ = v___x_1995_;
goto v___jp_1941_;
}
}
}
}
v___jp_1998_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_unsigned_to_nat(4u);
v___x_2015_ = l_Lean_Syntax_getArg(v___y_2001_, v___x_2014_);
lean_dec(v___y_2001_);
v___x_2016_ = l_Lean_Syntax_getOptional_x3f(v___x_2015_);
lean_dec(v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_box(0);
v___y_1973_ = v___y_2013_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2003_;
v___y_1976_ = v___y_2006_;
v___y_1977_ = v___y_2011_;
v___y_1978_ = v___y_2009_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2000_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v_args_2005_;
v___y_1984_ = v___y_2002_;
v___y_1985_ = v___y_2008_;
v___y_1986_ = v___y_2004_;
v___y_1987_ = v___x_2017_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_val_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
v___y_1973_ = v___y_2013_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2003_;
v___y_1976_ = v___y_2006_;
v___y_1977_ = v___y_2011_;
v___y_1978_ = v___y_2009_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2000_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v_args_2005_;
v___y_1984_ = v___y_2002_;
v___y_1985_ = v___y_2008_;
v___y_1986_ = v___y_2004_;
v___y_1987_ = v___x_2023_;
goto v___jp_1972_;
}
}
}
}
v___jp_2027_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_unsigned_to_nat(3u);
v___x_2043_ = l_Lean_Syntax_getArg(v___y_2030_, v___x_2042_);
v___x_2044_ = l_Lean_Syntax_isNone(v___x_2043_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
lean_inc(v___x_2043_);
v___x_2045_ = l_Lean_Syntax_matchesNull(v___x_2043_, v___x_2026_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v___x_2043_);
lean_dec(v_o_2033_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2047_ = l_Lean_Syntax_getArg(v___x_2043_, v___x_1229_);
lean_dec(v___x_2043_);
v___x_2048_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2049_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2048_);
lean_inc(v___x_2047_);
v___x_2050_ = l_Lean_Syntax_isOfKind(v___x_2047_, v___x_2049_);
lean_dec(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec(v___x_2047_);
lean_dec(v_o_2033_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2051_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_args_2053_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_Syntax_getArg(v___x_2047_, v___x_2026_);
lean_dec(v___x_2047_);
v_args_2053_ = l_Lean_Syntax_getArgs(v___x_2052_);
lean_dec(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_args_2053_);
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2030_;
v___y_2002_ = v_o_2033_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
v_args_2005_ = v___x_2054_;
v___y_2006_ = v___y_2034_;
v___y_2007_ = v___y_2035_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
goto v___jp_1998_;
}
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v___x_2043_);
v___x_2055_ = lean_box(0);
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2030_;
v___y_2002_ = v_o_2033_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
v_args_2005_ = v___x_2055_;
v___y_2006_ = v___y_2034_;
v___y_2007_ = v___y_2035_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
goto v___jp_1998_;
}
}
v___jp_2056_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2066_ = lean_unsigned_to_nat(2u);
v___x_2067_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_2066_);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2069_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2068_);
lean_inc(v___x_2067_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v___x_2067_, v___x_2069_);
lean_dec(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v___x_2067_);
lean_dec(v_bang_2057_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2071_;
}
else
{
lean_object* v_cfg_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_cfg_2072_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_1229_);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2074_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2073_);
lean_inc(v_cfg_2072_);
v___x_2075_ = l_Lean_Syntax_isOfKind(v_cfg_2072_, v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec(v_cfg_2072_);
lean_dec(v___x_2067_);
lean_dec(v_bang_2057_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2077_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2026_);
v___x_2078_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2066_);
v___x_2079_ = l_Lean_Syntax_isNone(v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
lean_inc(v___x_2078_);
v___x_2080_ = l_Lean_Syntax_matchesNull(v___x_2078_, v___x_2026_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v___x_2078_);
lean_dec(v___x_2077_);
lean_dec(v_cfg_2072_);
lean_dec(v___x_2067_);
lean_dec(v_bang_2057_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2081_;
}
else
{
lean_object* v_o_2082_; lean_object* v___x_2083_; 
v_o_2082_ = l_Lean_Syntax_getArg(v___x_2078_, v___x_1229_);
lean_dec(v___x_2078_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_o_2082_);
v___y_2028_ = v___x_2075_;
v___y_2029_ = v_bang_2057_;
v___y_2030_ = v___x_2067_;
v___y_2031_ = v___x_2077_;
v___y_2032_ = v_cfg_2072_;
v_o_2033_ = v___x_2083_;
v___y_2034_ = v___y_2058_;
v___y_2035_ = v___y_2059_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
goto v___jp_2027_;
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v___x_2078_);
v___x_2084_ = lean_box(0);
v___y_2028_ = v___x_2075_;
v___y_2029_ = v_bang_2057_;
v___y_2030_ = v___x_2067_;
v___y_2031_ = v___x_2077_;
v___y_2032_ = v_cfg_2072_;
v_o_2033_ = v___x_2084_;
v___y_2034_ = v___y_2058_;
v___y_2035_ = v___y_2059_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
goto v___jp_2027_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2092_, lean_object* v_stx_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v___f_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_40440__boxed_2108_; uint8_t v___x_40441__boxed_2109_; lean_object* v_res_2110_; 
v___x_40440__boxed_2108_ = lean_unbox(v___x_2092_);
v___x_40441__boxed_2109_ = lean_unbox(v___x_2094_);
v_res_2110_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40440__boxed_2108_, v_stx_2093_, v___x_40441__boxed_2109_, v___x_2095_, v___x_2096_, v___x_2097_, v___f_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_stx_2093_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___y_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2120_);
v___x_2134_ = l_Lean_Syntax_isOfKind(v_stx_2120_, v___x_2133_);
v___x_2135_ = 1;
v___f_2136_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2137_ = lean_box(v___x_2134_);
v___x_2138_ = lean_box(v___x_2135_);
v___y_2139_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2139_, 0, v___x_2137_);
lean_closure_set(v___y_2139_, 1, v_stx_2120_);
lean_closure_set(v___y_2139_, 2, v___x_2138_);
lean_closure_set(v___y_2139_, 3, v___x_2130_);
lean_closure_set(v___y_2139_, 4, v___x_2131_);
lean_closure_set(v___y_2139_, 5, v___x_2132_);
lean_closure_set(v___y_2139_, 6, v___f_2136_);
v___x_2140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2140_, 0, v___y_2139_);
v___x_2141_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2140_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2153_, lean_object* v_as_2154_, lean_object* v_as_x27_2155_, lean_object* v_b_2156_, lean_object* v_a_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2153_, v_as_x27_2155_, v_b_2156_, v___y_2164_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2168_, lean_object* v_as_2169_, lean_object* v_as_x27_2170_, lean_object* v_b_2171_, lean_object* v_a_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2168_, v_as_2169_, v_as_x27_2170_, v_b_2171_, v_a_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v_as_x27_2170_);
lean_dec(v_as_2169_);
lean_dec(v___x_2168_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2183_, lean_object* v_ref_2184_, lean_object* v_msg_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2184_, v_msg_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_ref_2197_, lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2196_, v_ref_2197_, v_msg_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v_ref_2197_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2209_, lean_object* v_ref_2210_, lean_object* v_constName_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2210_, v_constName_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_ref_2223_, lean_object* v_constName_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2222_, v_ref_2223_, v_constName_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v_ref_2223_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2235_, lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2236_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_msg_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2247_, v_msg_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2259_, v___y_2266_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_opt_2270_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2281_, lean_object* v_ref_2282_, lean_object* v_msg_2283_, lean_object* v_declHint_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2282_, v_msg_2283_, v_declHint_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2295_, lean_object* v_ref_2296_, lean_object* v_msg_2297_, lean_object* v_declHint_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2295_, v_ref_2296_, v_msg_2297_, v_declHint_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v_ref_2296_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2309_, lean_object* v_declHint_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2309_, v_declHint_2310_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2321_, lean_object* v_declHint_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2321_, v_declHint_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2333_, lean_object* v_msgData_2334_, uint8_t v_severity_2335_, uint8_t v_isSilent_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2333_, v_msgData_2334_, v_severity_2335_, v_isSilent_2336_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2347_, lean_object* v_msgData_2348_, lean_object* v_severity_2349_, lean_object* v_isSilent_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_severity_boxed_2360_; uint8_t v_isSilent_boxed_2361_; lean_object* v_res_2362_; 
v_severity_boxed_2360_ = lean_unbox(v_severity_2349_);
v_isSilent_boxed_2361_ = lean_unbox(v_isSilent_2350_);
v_res_2362_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2347_, v_msgData_2348_, v_severity_boxed_2360_, v_isSilent_boxed_2361_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_ref_2347_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2370_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2371_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2373_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2374_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2405_ = l_Lean_addBuiltinDeclarationRanges(v___x_2403_, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2408_, lean_object* v_as_x27_2409_, lean_object* v_b_2410_, lean_object* v___y_2411_){
_start:
{
if (lean_obj_tag(v_as_x27_2409_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2410_);
return v___x_2413_;
}
else
{
lean_object* v_head_2414_; lean_object* v_tail_2415_; lean_object* v_ref_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_head_2414_ = lean_ctor_get(v_as_x27_2409_, 0);
v_tail_2415_ = lean_ctor_get(v_as_x27_2409_, 1);
v_ref_2416_ = lean_ctor_get(v___y_2411_, 5);
v___x_2417_ = 1;
v___x_2418_ = 0;
v___x_2419_ = l_Lean_SourceInfo_fromRef(v_ref_2416_, v___x_2418_);
v___x_2420_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2421_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2422_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2419_);
v___x_2423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2419_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
lean_ctor_set(v___x_2423_, 2, v___x_2422_);
lean_inc(v_head_2414_);
v___x_2424_ = l_Lean_mkCIdentFrom(v___x_2408_, v_head_2414_, v___x_2417_);
lean_inc_ref(v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node3(v___x_2419_, v___x_2420_, v___x_2423_, v___x_2423_, v___x_2424_);
v___x_2426_ = lean_array_push(v_b_2410_, v___x_2425_);
v_as_x27_2409_ = v_tail_2415_;
v_b_2410_ = v___x_2426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2428_, lean_object* v_as_x27_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2428_, v_as_x27_2429_, v_b_2430_, v___y_2431_);
lean_dec_ref(v___y_2431_);
lean_dec(v_as_x27_2429_);
lean_dec(v___x_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_b_2437_);
return v___x_2448_;
}
else
{
lean_object* v_a_2449_; lean_object* v_name_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2449_ = lean_array_uget_borrowed(v_as_2434_, v_i_2436_);
v_name_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_name_2450_);
v___x_2451_ = lean_mk_syntax_ident(v_name_2450_);
lean_inc(v___x_2451_);
v___x_2452_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2451_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2451_, v_a_2453_, v_b_2437_, v___y_2444_);
lean_dec(v_a_2453_);
lean_dec(v___x_2451_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; size_t v___x_2456_; size_t v___x_2457_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2436_, v___x_2456_);
v_i_2436_ = v___x_2457_;
v_b_2437_ = v_a_2455_;
goto _start;
}
else
{
return v___x_2454_;
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v___x_2451_);
lean_dec_ref(v_b_2437_);
v_a_2459_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2452_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2452_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2467_, lean_object* v_sz_2468_, lean_object* v_i_2469_, lean_object* v_b_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
size_t v_sz_boxed_2480_; size_t v_i_boxed_2481_; lean_object* v_res_2482_; 
v_sz_boxed_2480_ = lean_unbox_usize(v_sz_2468_);
lean_dec(v_sz_2468_);
v_i_boxed_2481_ = lean_unbox_usize(v_i_2469_);
lean_dec(v_i_2469_);
v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2467_, v_sz_boxed_2480_, v_i_boxed_2481_, v_b_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v_as_2467_);
return v_res_2482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2486_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_unsigned_to_nat(32u);
v___x_2490_ = lean_mk_empty_array_with_capacity(v___x_2489_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2492_ = ((size_t)5ULL);
v___x_2493_ = lean_unsigned_to_nat(0u);
v___x_2494_ = lean_unsigned_to_nat(32u);
v___x_2495_ = lean_mk_empty_array_with_capacity(v___x_2494_);
v___x_2496_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2497_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2495_);
lean_ctor_set(v___x_2497_, 2, v___x_2493_);
lean_ctor_set(v___x_2497_, 3, v___x_2493_);
lean_ctor_set_usize(v___x_2497_, 4, v___x_2492_);
return v___x_2497_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2499_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
lean_ctor_set(v___x_2500_, 2, v___x_2499_);
lean_ctor_set(v___x_2500_, 3, v___x_2498_);
return v___x_2500_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2502_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2512_, lean_object* v_stx_2513_, uint8_t v___x_2514_, lean_object* v___x_2515_, lean_object* v___x_2516_, lean_object* v___x_2517_, lean_object* v___f_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
if (v___x_2512_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_2528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; lean_object* v_tk_2530_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; lean_object* v_stxForSuggestion_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; uint8_t v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; uint8_t v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; uint8_t v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; uint8_t v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; uint8_t v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; uint8_t v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; uint8_t v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; uint8_t v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; uint8_t v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; uint8_t v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; uint8_t v___y_2941_; lean_object* v___y_2942_; uint8_t v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; uint8_t v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; uint8_t v___y_2958_; uint8_t v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_2990_; lean_object* v_stxForExecution_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; uint8_t v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; uint8_t v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; uint8_t v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; uint8_t v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; uint8_t v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; uint8_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; uint8_t v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; uint8_t v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; uint8_t v___y_3292_; lean_object* v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; uint8_t v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; uint8_t v___y_3338_; lean_object* v___y_3339_; lean_object* v_argsArray_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3366_; uint8_t v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v_args_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___x_3494_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; lean_object* v_o_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v_bang_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v_tk_2530_ = l_Lean_Syntax_getArg(v_stx_2513_, v___x_2529_);
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3553_ = l_Lean_Syntax_getArg(v_stx_2513_, v___x_3494_);
v___x_3554_ = l_Lean_Syntax_isNone(v___x_3553_);
if (v___x_3554_ == 0)
{
uint8_t v___x_3555_; 
lean_inc(v___x_3553_);
v___x_3555_ = l_Lean_Syntax_matchesNull(v___x_3553_, v___x_3494_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec(v___x_3553_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3556_;
}
else
{
lean_object* v_bang_3557_; lean_object* v___x_3558_; 
v_bang_3557_ = l_Lean_Syntax_getArg(v___x_3553_, v___x_2529_);
lean_dec(v___x_3553_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_bang_3557_);
v_bang_3525_ = v___x_3558_;
v___y_3526_ = v___y_2519_;
v___y_3527_ = v___y_2520_;
v___y_3528_ = v___y_2521_;
v___y_3529_ = v___y_2522_;
v___y_3530_ = v___y_2523_;
v___y_3531_ = v___y_2524_;
v___y_3532_ = v___y_2525_;
v___y_3533_ = v___y_2526_;
goto v___jp_3524_;
}
}
else
{
lean_object* v___x_3559_; 
lean_dec(v___x_3553_);
v___x_3559_ = lean_box(0);
v_bang_3525_ = v___x_3559_;
v___y_3526_ = v___y_2519_;
v___y_3527_ = v___y_2520_;
v___y_3528_ = v___y_2521_;
v___y_3529_ = v___y_2522_;
v___y_3530_ = v___y_2523_;
v___y_3531_ = v___y_2524_;
v___y_3532_ = v___y_2525_;
v___y_3533_ = v___y_2526_;
goto v___jp_3524_;
}
v___jp_2531_:
{
lean_object* v_usedTheorems_2538_; lean_object* v_diag_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2580_; 
v_usedTheorems_2538_ = lean_ctor_get(v___y_2533_, 0);
v_diag_2539_ = lean_ctor_get(v___y_2533_, 1);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___y_2533_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2541_ = v___y_2533_;
v_isShared_2542_ = v_isSharedCheck_2580_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_diag_2539_);
lean_inc(v_usedTheorems_2538_);
lean_dec(v___y_2533_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2580_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2532_, v_usedTheorems_2538_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec_ref(v_usedTheorems_2538_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v_ref_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v_ref_2545_ = lean_ctor_get(v___y_2536_, 5);
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v_a_2544_);
lean_ctor_set(v___x_2541_, 0, v___x_2546_);
v___x_2548_ = v___x_2541_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_a_2544_);
v___x_2548_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
lean_ctor_set(v___x_2550_, 3, v___x_2549_);
lean_ctor_set(v___x_2550_, 4, v___x_2549_);
lean_ctor_set(v___x_2550_, 5, v___x_2549_);
lean_inc(v_ref_2545_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_ref_2545_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2553_ = 4;
v___x_2554_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2530_, v___x_2550_, v___x_2551_, v___x_2552_, v___x_2549_, v___x_2553_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2562_);
v___x_2556_ = v___x_2554_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v___x_2554_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_diag_2539_);
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_diag_2539_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_diag_2539_);
v_a_2563_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2554_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2554_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_del_object(v___x_2541_);
lean_dec_ref(v_diag_2539_);
lean_dec(v_tk_2530_);
v_a_2572_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2543_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2543_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
v___jp_2581_:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2586_, v___y_2588_, v___y_2583_, v___y_2582_, v___y_2587_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2593_ = l_Lean_Meta_simpAll(v_a_2591_, v___y_2589_, v___y_2584_, v___x_2592_, v___y_2588_, v___y_2583_, v___y_2582_, v___y_2587_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_fst_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v_fst_2595_ = lean_ctor_get(v_a_2594_, 0);
if (lean_obj_tag(v_fst_2595_) == 0)
{
lean_object* v_snd_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_snd_2596_ = lean_ctor_get(v_a_2594_, 1);
lean_inc(v_snd_2596_);
lean_dec(v_a_2594_);
v___x_2597_ = lean_box(0);
v___x_2598_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2597_, v___y_2586_, v___y_2588_, v___y_2583_, v___y_2582_, v___y_2587_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_dec_ref(v___x_2598_);
v___y_2532_ = v___y_2585_;
v___y_2533_ = v_snd_2596_;
v___y_2534_ = v___y_2588_;
v___y_2535_ = v___y_2583_;
v___y_2536_ = v___y_2582_;
v___y_2537_ = v___y_2587_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_snd_2596_);
lean_dec(v___y_2585_);
lean_dec(v_tk_2530_);
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_snd_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2625_; 
lean_inc_ref(v_fst_2595_);
v_snd_2607_ = lean_ctor_get(v_a_2594_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_a_2594_, 0);
lean_dec(v_unused_2626_);
v___x_2609_ = v_a_2594_;
v_isShared_2610_ = v_isSharedCheck_2625_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_snd_2607_);
lean_dec(v_a_2594_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2625_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_val_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v_val_2611_ = lean_ctor_get(v_fst_2595_, 0);
lean_inc(v_val_2611_);
lean_dec_ref(v_fst_2595_);
v___x_2612_ = lean_box(0);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 1, v___x_2612_);
lean_ctor_set(v___x_2609_, 0, v_val_2611_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_val_2611_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2614_, v___y_2586_, v___y_2588_, v___y_2583_, v___y_2582_, v___y_2587_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2532_ = v___y_2585_;
v___y_2533_ = v_snd_2607_;
v___y_2534_ = v___y_2588_;
v___y_2535_ = v___y_2583_;
v___y_2536_ = v___y_2582_;
v___y_2537_ = v___y_2587_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_snd_2607_);
lean_dec(v___y_2585_);
lean_dec(v_tk_2530_);
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v___y_2585_);
lean_dec(v_tk_2530_);
v_a_2627_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2593_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2593_);
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
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v_tk_2530_);
v_a_2635_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2590_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2590_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
v___jp_2643_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2658_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2646_, v___x_2514_, v___y_2644_, v___x_2514_, v___x_2657_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2646_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
if (lean_obj_tag(v___y_2645_) == 0)
{
lean_object* v_ctx_2660_; lean_object* v_simprocs_2661_; 
v_ctx_2660_ = lean_ctor_get(v_a_2659_, 0);
lean_inc_ref(v_ctx_2660_);
v_simprocs_2661_ = lean_ctor_get(v_a_2659_, 1);
lean_inc_ref(v_simprocs_2661_);
lean_dec(v_a_2659_);
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2654_;
v___y_2584_ = v_simprocs_2661_;
v___y_2585_ = v_stxForSuggestion_2648_;
v___y_2586_ = v___y_2650_;
v___y_2587_ = v___y_2656_;
v___y_2588_ = v___y_2653_;
v___y_2589_ = v_ctx_2660_;
goto v___jp_2581_;
}
else
{
lean_dec_ref(v___y_2645_);
if (v___y_2647_ == 0)
{
lean_object* v_ctx_2662_; lean_object* v_simprocs_2663_; 
v_ctx_2662_ = lean_ctor_get(v_a_2659_, 0);
lean_inc_ref(v_ctx_2662_);
v_simprocs_2663_ = lean_ctor_get(v_a_2659_, 1);
lean_inc_ref(v_simprocs_2663_);
lean_dec(v_a_2659_);
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2654_;
v___y_2584_ = v_simprocs_2663_;
v___y_2585_ = v_stxForSuggestion_2648_;
v___y_2586_ = v___y_2650_;
v___y_2587_ = v___y_2656_;
v___y_2588_ = v___y_2653_;
v___y_2589_ = v_ctx_2662_;
goto v___jp_2581_;
}
else
{
lean_object* v_ctx_2664_; lean_object* v_simprocs_2665_; lean_object* v___x_2666_; 
v_ctx_2664_ = lean_ctor_get(v_a_2659_, 0);
lean_inc_ref(v_ctx_2664_);
v_simprocs_2665_ = lean_ctor_get(v_a_2659_, 1);
lean_inc_ref(v_simprocs_2665_);
lean_dec(v_a_2659_);
v___x_2666_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2664_);
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2654_;
v___y_2584_ = v_simprocs_2665_;
v___y_2585_ = v_stxForSuggestion_2648_;
v___y_2586_ = v___y_2650_;
v___y_2587_ = v___y_2656_;
v___y_2588_ = v___y_2653_;
v___y_2589_ = v___x_2666_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_stxForSuggestion_2648_);
lean_dec(v___y_2645_);
lean_dec(v_tk_2530_);
v_a_2667_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2658_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2658_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
v___jp_2675_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_inc_ref_n(v___y_2685_, 2);
v___x_2696_ = l_Array_append___redArg(v___y_2685_, v___y_2695_);
lean_dec_ref(v___y_2695_);
lean_inc_n(v___y_2693_, 2);
lean_inc_n(v___y_2678_, 2);
v___x_2697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2678_);
lean_ctor_set(v___x_2697_, 1, v___y_2693_);
lean_ctor_set(v___x_2697_, 2, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2698_, 0, v___y_2678_);
lean_ctor_set(v___x_2698_, 1, v___y_2693_);
lean_ctor_set(v___x_2698_, 2, v___y_2685_);
v___x_2699_ = l_Lean_Syntax_node5(v___y_2678_, v___y_2679_, v___y_2692_, v___y_2694_, v___y_2683_, v___x_2697_, v___x_2698_);
v___y_2644_ = v___y_2676_;
v___y_2645_ = v___y_2690_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2687_;
v_stxForSuggestion_2648_ = v___x_2699_;
v___y_2649_ = v___y_2677_;
v___y_2650_ = v___y_2688_;
v___y_2651_ = v___y_2686_;
v___y_2652_ = v___y_2680_;
v___y_2653_ = v___y_2681_;
v___y_2654_ = v___y_2684_;
v___y_2655_ = v___y_2689_;
v___y_2656_ = v___y_2682_;
goto v___jp_2643_;
}
v___jp_2700_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_inc_ref(v___y_2709_);
v___x_2721_ = l_Array_append___redArg(v___y_2709_, v___y_2720_);
lean_dec_ref(v___y_2720_);
lean_inc(v___y_2719_);
lean_inc(v___y_2703_);
v___x_2722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2722_, 0, v___y_2703_);
lean_ctor_set(v___x_2722_, 1, v___y_2719_);
lean_ctor_set(v___x_2722_, 2, v___x_2721_);
if (lean_obj_tag(v___y_2713_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_val_2723_ = lean_ctor_get(v___y_2713_, 0);
lean_inc(v_val_2723_);
lean_dec_ref(v___y_2713_);
v___x_2724_ = l_Lean_SourceInfo_fromRef(v_val_2723_, v___x_2514_);
lean_dec(v_val_2723_);
v___x_2725_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Array_mkArray1___redArg(v___x_2726_);
v___y_2676_ = v___y_2701_;
v___y_2677_ = v___y_2702_;
v___y_2678_ = v___y_2703_;
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___x_2722_;
v___y_2684_ = v___y_2708_;
v___y_2685_ = v___y_2709_;
v___y_2686_ = v___y_2710_;
v___y_2687_ = v___y_2711_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2717_;
v___y_2692_ = v___y_2716_;
v___y_2693_ = v___y_2719_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___x_2727_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2728_; 
lean_dec(v___y_2713_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2676_ = v___y_2701_;
v___y_2677_ = v___y_2702_;
v___y_2678_ = v___y_2703_;
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___x_2722_;
v___y_2684_ = v___y_2708_;
v___y_2685_ = v___y_2709_;
v___y_2686_ = v___y_2710_;
v___y_2687_ = v___y_2711_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2717_;
v___y_2692_ = v___y_2716_;
v___y_2693_ = v___y_2719_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___x_2728_;
goto v___jp_2675_;
}
}
v___jp_2729_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_inc_ref_n(v___y_2742_, 2);
v___x_2751_ = l_Array_append___redArg(v___y_2742_, v___y_2750_);
lean_dec_ref(v___y_2750_);
lean_inc_n(v___y_2737_, 3);
lean_inc_n(v___y_2733_, 5);
v___x_2752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2752_, 0, v___y_2733_);
lean_ctor_set(v___x_2752_, 1, v___y_2737_);
lean_ctor_set(v___x_2752_, 2, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___y_2733_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2756_ = l_Lean_Syntax_SepArray_ofElems(v___x_2755_, v___y_2744_);
lean_dec_ref(v___y_2744_);
v___x_2757_ = l_Array_append___redArg(v___y_2742_, v___x_2756_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2758_, 0, v___y_2733_);
lean_ctor_set(v___x_2758_, 1, v___y_2737_);
lean_ctor_set(v___x_2758_, 2, v___x_2757_);
v___x_2759_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2733_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_Syntax_node3(v___y_2733_, v___y_2737_, v___x_2754_, v___x_2758_, v___x_2760_);
v___x_2762_ = l_Lean_Syntax_node5(v___y_2733_, v___y_2746_, v___y_2748_, v___y_2749_, v___y_2734_, v___x_2752_, v___x_2761_);
v___y_2644_ = v___y_2730_;
v___y_2645_ = v___y_2745_;
v___y_2646_ = v___y_2747_;
v___y_2647_ = v___y_2740_;
v_stxForSuggestion_2648_ = v___x_2762_;
v___y_2649_ = v___y_2731_;
v___y_2650_ = v___y_2741_;
v___y_2651_ = v___y_2739_;
v___y_2652_ = v___y_2732_;
v___y_2653_ = v___y_2735_;
v___y_2654_ = v___y_2738_;
v___y_2655_ = v___y_2743_;
v___y_2656_ = v___y_2736_;
goto v___jp_2643_;
}
v___jp_2763_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_inc_ref(v___y_2775_);
v___x_2785_ = l_Array_append___redArg(v___y_2775_, v___y_2784_);
lean_dec_ref(v___y_2784_);
lean_inc(v___y_2769_);
lean_inc(v___y_2767_);
v___x_2786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___y_2767_);
lean_ctor_set(v___x_2786_, 1, v___y_2769_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
if (lean_obj_tag(v___y_2776_) == 1)
{
lean_object* v_val_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_val_2787_ = lean_ctor_get(v___y_2776_, 0);
lean_inc(v_val_2787_);
lean_dec_ref(v___y_2776_);
v___x_2788_ = l_Lean_SourceInfo_fromRef(v_val_2787_, v___x_2514_);
lean_dec(v_val_2787_);
v___x_2789_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_Array_mkArray1___redArg(v___x_2790_);
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___x_2786_;
v___y_2735_ = v___y_2768_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2769_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___y_2772_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2775_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2791_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2792_; 
lean_dec(v___y_2776_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___x_2786_;
v___y_2735_ = v___y_2768_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2769_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___y_2772_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2775_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2792_;
goto v___jp_2729_;
}
}
v___jp_2793_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_inc_ref_n(v___y_2800_, 2);
v___x_2815_ = l_Array_append___redArg(v___y_2800_, v___y_2814_);
lean_dec_ref(v___y_2814_);
lean_inc_n(v___y_2796_, 3);
lean_inc_n(v___y_2803_, 5);
v___x_2816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2816_, 0, v___y_2803_);
lean_ctor_set(v___x_2816_, 1, v___y_2796_);
lean_ctor_set(v___x_2816_, 2, v___x_2815_);
v___x_2817_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___y_2803_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2820_ = l_Lean_Syntax_SepArray_ofElems(v___x_2819_, v___y_2810_);
lean_dec_ref(v___y_2810_);
v___x_2821_ = l_Array_append___redArg(v___y_2800_, v___x_2820_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2822_, 0, v___y_2803_);
lean_ctor_set(v___x_2822_, 1, v___y_2796_);
lean_ctor_set(v___x_2822_, 2, v___x_2821_);
v___x_2823_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___y_2803_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_Syntax_node3(v___y_2803_, v___y_2796_, v___x_2818_, v___x_2822_, v___x_2824_);
v___x_2826_ = l_Lean_Syntax_node5(v___y_2803_, v___y_2804_, v___y_2801_, v___y_2813_, v___y_2808_, v___x_2816_, v___x_2825_);
v___y_2644_ = v___y_2794_;
v___y_2645_ = v___y_2811_;
v___y_2646_ = v___y_2812_;
v___y_2647_ = v___y_2806_;
v_stxForSuggestion_2648_ = v___x_2826_;
v___y_2649_ = v___y_2795_;
v___y_2650_ = v___y_2807_;
v___y_2651_ = v___y_2805_;
v___y_2652_ = v___y_2797_;
v___y_2653_ = v___y_2798_;
v___y_2654_ = v___y_2802_;
v___y_2655_ = v___y_2809_;
v___y_2656_ = v___y_2799_;
goto v___jp_2643_;
}
v___jp_2827_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_inc_ref(v___y_2833_);
v___x_2849_ = l_Array_append___redArg(v___y_2833_, v___y_2848_);
lean_dec_ref(v___y_2848_);
lean_inc(v___y_2830_);
lean_inc(v___y_2837_);
v___x_2850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2850_, 0, v___y_2837_);
lean_ctor_set(v___x_2850_, 1, v___y_2830_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
if (lean_obj_tag(v___y_2842_) == 1)
{
lean_object* v_val_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_val_2851_ = lean_ctor_get(v___y_2842_, 0);
lean_inc(v_val_2851_);
lean_dec_ref(v___y_2842_);
v___x_2852_ = l_Lean_SourceInfo_fromRef(v_val_2851_, v___x_2514_);
lean_dec(v_val_2851_);
v___x_2853_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Array_mkArray1___redArg(v___x_2854_);
v___y_2794_ = v___y_2828_;
v___y_2795_ = v___y_2829_;
v___y_2796_ = v___y_2830_;
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2832_;
v___y_2799_ = v___y_2834_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2835_;
v___y_2802_ = v___y_2836_;
v___y_2803_ = v___y_2837_;
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___x_2850_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___x_2855_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2856_; 
lean_dec(v___y_2842_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2794_ = v___y_2828_;
v___y_2795_ = v___y_2829_;
v___y_2796_ = v___y_2830_;
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2832_;
v___y_2799_ = v___y_2834_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2835_;
v___y_2802_ = v___y_2836_;
v___y_2803_ = v___y_2837_;
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___x_2850_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___x_2856_;
goto v___jp_2793_;
}
}
v___jp_2857_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_inc_ref_n(v___y_2864_, 2);
v___x_2878_ = l_Array_append___redArg(v___y_2864_, v___y_2877_);
lean_dec_ref(v___y_2877_);
lean_inc_n(v___y_2869_, 2);
lean_inc_n(v___y_2872_, 2);
v___x_2879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2879_, 0, v___y_2872_);
lean_ctor_set(v___x_2879_, 1, v___y_2869_);
lean_ctor_set(v___x_2879_, 2, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2880_, 0, v___y_2872_);
lean_ctor_set(v___x_2880_, 1, v___y_2869_);
lean_ctor_set(v___x_2880_, 2, v___y_2864_);
v___x_2881_ = l_Lean_Syntax_node5(v___y_2872_, v___y_2870_, v___y_2865_, v___y_2876_, v___y_2873_, v___x_2879_, v___x_2880_);
v___y_2644_ = v___y_2858_;
v___y_2645_ = v___y_2874_;
v___y_2646_ = v___y_2875_;
v___y_2647_ = v___y_2867_;
v_stxForSuggestion_2648_ = v___x_2881_;
v___y_2649_ = v___y_2859_;
v___y_2650_ = v___y_2868_;
v___y_2651_ = v___y_2866_;
v___y_2652_ = v___y_2860_;
v___y_2653_ = v___y_2861_;
v___y_2654_ = v___y_2863_;
v___y_2655_ = v___y_2871_;
v___y_2656_ = v___y_2862_;
goto v___jp_2643_;
}
v___jp_2882_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_inc_ref(v___y_2889_);
v___x_2903_ = l_Array_append___redArg(v___y_2889_, v___y_2902_);
lean_dec_ref(v___y_2902_);
lean_inc(v___y_2894_);
lean_inc(v___y_2898_);
v___x_2904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2904_, 0, v___y_2898_);
lean_ctor_set(v___x_2904_, 1, v___y_2894_);
lean_ctor_set(v___x_2904_, 2, v___x_2903_);
if (lean_obj_tag(v___y_2896_) == 1)
{
lean_object* v_val_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_val_2905_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v___y_2896_);
v___x_2906_ = l_Lean_SourceInfo_fromRef(v_val_2905_, v___x_2514_);
lean_dec(v_val_2905_);
v___x_2907_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Array_mkArray1___redArg(v___x_2908_);
v___y_2858_ = v___y_2883_;
v___y_2859_ = v___y_2884_;
v___y_2860_ = v___y_2885_;
v___y_2861_ = v___y_2886_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___y_2888_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___y_2897_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___x_2904_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___y_2900_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___x_2909_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2910_; 
lean_dec(v___y_2896_);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2858_ = v___y_2883_;
v___y_2859_ = v___y_2884_;
v___y_2860_ = v___y_2885_;
v___y_2861_ = v___y_2886_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___y_2888_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___y_2897_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___x_2904_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___y_2900_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___x_2910_;
goto v___jp_2857_;
}
}
v___jp_2911_:
{
lean_object* v_ref_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_ref_2928_ = lean_ctor_get(v___y_2923_, 5);
v___x_2929_ = l_Lean_SourceInfo_fromRef(v_ref_2928_, v___y_2927_);
v___x_2930_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2931_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_2930_);
v___x_2932_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2936_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2937_; lean_object* v___x_2938_; 
v_val_2937_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2937_);
lean_dec_ref(v___y_2920_);
v___x_2938_ = l_Array_mkArray1___redArg(v_val_2937_);
v___y_2701_ = v___y_2912_;
v___y_2702_ = v___y_2913_;
v___y_2703_ = v___x_2929_;
v___y_2704_ = v___x_2931_;
v___y_2705_ = v___y_2914_;
v___y_2706_ = v___y_2915_;
v___y_2707_ = v___y_2916_;
v___y_2708_ = v___y_2917_;
v___y_2709_ = v___x_2936_;
v___y_2710_ = v___y_2918_;
v___y_2711_ = v___y_2919_;
v___y_2712_ = v___y_2921_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2934_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___x_2935_;
v___y_2720_ = v___x_2938_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2939_; 
lean_dec(v___y_2920_);
v___x_2939_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2701_ = v___y_2912_;
v___y_2702_ = v___y_2913_;
v___y_2703_ = v___x_2929_;
v___y_2704_ = v___x_2931_;
v___y_2705_ = v___y_2914_;
v___y_2706_ = v___y_2915_;
v___y_2707_ = v___y_2916_;
v___y_2708_ = v___y_2917_;
v___y_2709_ = v___x_2936_;
v___y_2710_ = v___y_2918_;
v___y_2711_ = v___y_2919_;
v___y_2712_ = v___y_2921_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2934_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___x_2935_;
v___y_2720_ = v___x_2939_;
goto v___jp_2700_;
}
}
v___jp_2940_:
{
if (v___y_2958_ == 0)
{
lean_object* v_ref_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_ref_2959_ = lean_ctor_get(v___y_2953_, 5);
v___x_2960_ = l_Lean_SourceInfo_fromRef(v_ref_2959_, v___y_2958_);
v___x_2961_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2962_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_2961_);
v___x_2963_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2967_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2950_) == 1)
{
lean_object* v_val_2968_; lean_object* v___x_2969_; 
v_val_2968_ = lean_ctor_get(v___y_2950_, 0);
lean_inc(v_val_2968_);
lean_dec_ref(v___y_2950_);
v___x_2969_ = l_Array_mkArray1___redArg(v_val_2968_);
v___y_2764_ = v___y_2941_;
v___y_2765_ = v___y_2942_;
v___y_2766_ = v___y_2944_;
v___y_2767_ = v___x_2960_;
v___y_2768_ = v___y_2945_;
v___y_2769_ = v___x_2966_;
v___y_2770_ = v___y_2946_;
v___y_2771_ = v___y_2947_;
v___y_2772_ = v___y_2948_;
v___y_2773_ = v___y_2949_;
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___x_2967_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___x_2962_;
v___y_2780_ = v___y_2955_;
v___y_2781_ = v___y_2956_;
v___y_2782_ = v___x_2965_;
v___y_2783_ = v___y_2957_;
v___y_2784_ = v___x_2969_;
goto v___jp_2763_;
}
else
{
lean_object* v___x_2970_; 
lean_dec(v___y_2950_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2764_ = v___y_2941_;
v___y_2765_ = v___y_2942_;
v___y_2766_ = v___y_2944_;
v___y_2767_ = v___x_2960_;
v___y_2768_ = v___y_2945_;
v___y_2769_ = v___x_2966_;
v___y_2770_ = v___y_2946_;
v___y_2771_ = v___y_2947_;
v___y_2772_ = v___y_2948_;
v___y_2773_ = v___y_2949_;
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___x_2967_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2953_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___x_2962_;
v___y_2780_ = v___y_2955_;
v___y_2781_ = v___y_2956_;
v___y_2782_ = v___x_2965_;
v___y_2783_ = v___y_2957_;
v___y_2784_ = v___x_2970_;
goto v___jp_2763_;
}
}
else
{
lean_object* v_ref_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_ref_2971_ = lean_ctor_get(v___y_2953_, 5);
v___x_2972_ = l_Lean_SourceInfo_fromRef(v_ref_2971_, v___y_2943_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2974_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_2973_);
v___x_2975_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2979_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2950_) == 1)
{
lean_object* v_val_2980_; lean_object* v___x_2981_; 
v_val_2980_ = lean_ctor_get(v___y_2950_, 0);
lean_inc(v_val_2980_);
lean_dec_ref(v___y_2950_);
v___x_2981_ = l_Array_mkArray1___redArg(v_val_2980_);
v___y_2828_ = v___y_2941_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___x_2978_;
v___y_2831_ = v___y_2944_;
v___y_2832_ = v___y_2945_;
v___y_2833_ = v___x_2979_;
v___y_2834_ = v___y_2946_;
v___y_2835_ = v___x_2977_;
v___y_2836_ = v___y_2947_;
v___y_2837_ = v___x_2972_;
v___y_2838_ = v___x_2974_;
v___y_2839_ = v___y_2948_;
v___y_2840_ = v___y_2949_;
v___y_2841_ = v___y_2951_;
v___y_2842_ = v___y_2952_;
v___y_2843_ = v___y_2953_;
v___y_2844_ = v___y_2954_;
v___y_2845_ = v___y_2955_;
v___y_2846_ = v___y_2956_;
v___y_2847_ = v___y_2957_;
v___y_2848_ = v___x_2981_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2982_; 
lean_dec(v___y_2950_);
v___x_2982_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2828_ = v___y_2941_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___x_2978_;
v___y_2831_ = v___y_2944_;
v___y_2832_ = v___y_2945_;
v___y_2833_ = v___x_2979_;
v___y_2834_ = v___y_2946_;
v___y_2835_ = v___x_2977_;
v___y_2836_ = v___y_2947_;
v___y_2837_ = v___x_2972_;
v___y_2838_ = v___x_2974_;
v___y_2839_ = v___y_2948_;
v___y_2840_ = v___y_2949_;
v___y_2841_ = v___y_2951_;
v___y_2842_ = v___y_2952_;
v___y_2843_ = v___y_2953_;
v___y_2844_ = v___y_2954_;
v___y_2845_ = v___y_2955_;
v___y_2846_ = v___y_2956_;
v___y_2847_ = v___y_2957_;
v___y_2848_ = v___x_2982_;
goto v___jp_2827_;
}
}
}
v___jp_2983_:
{
lean_object* v___x_3000_; lean_object* v_a_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3000_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2986_);
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = lean_array_get_size(v___y_2987_);
v___x_3003_ = lean_nat_dec_eq(v___x_3002_, v___x_2529_);
if (v___x_3003_ == 0)
{
if (lean_obj_tag(v___y_2988_) == 0)
{
v___y_2941_ = v___y_2984_;
v___y_2942_ = v___y_2992_;
v___y_2943_ = v___x_3003_;
v___y_2944_ = v___y_2995_;
v___y_2945_ = v___y_2996_;
v___y_2946_ = v___y_2999_;
v___y_2947_ = v___y_2997_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2989_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___y_2993_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2998_;
v___y_2954_ = v___y_2987_;
v___y_2955_ = v___y_2988_;
v___y_2956_ = v_stxForExecution_2991_;
v___y_2957_ = v_a_3001_;
v___y_2958_ = v___x_3003_;
goto v___jp_2940_;
}
else
{
v___y_2941_ = v___y_2984_;
v___y_2942_ = v___y_2992_;
v___y_2943_ = v___x_3003_;
v___y_2944_ = v___y_2995_;
v___y_2945_ = v___y_2996_;
v___y_2946_ = v___y_2999_;
v___y_2947_ = v___y_2997_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2989_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___y_2993_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2998_;
v___y_2954_ = v___y_2987_;
v___y_2955_ = v___y_2988_;
v___y_2956_ = v_stxForExecution_2991_;
v___y_2957_ = v_a_3001_;
v___y_2958_ = v___y_2989_;
goto v___jp_2940_;
}
}
else
{
lean_dec_ref(v___y_2987_);
if (lean_obj_tag(v___y_2988_) == 0)
{
uint8_t v___x_3004_; 
v___x_3004_ = 0;
v___y_2912_ = v___y_2984_;
v___y_2913_ = v___y_2992_;
v___y_2914_ = v___y_2995_;
v___y_2915_ = v___y_2996_;
v___y_2916_ = v___y_2999_;
v___y_2917_ = v___y_2997_;
v___y_2918_ = v___y_2994_;
v___y_2919_ = v___y_2989_;
v___y_2920_ = v___y_2990_;
v___y_2921_ = v___y_2993_;
v___y_2922_ = v___y_2985_;
v___y_2923_ = v___y_2998_;
v___y_2924_ = v___y_2988_;
v___y_2925_ = v_stxForExecution_2991_;
v___y_2926_ = v_a_3001_;
v___y_2927_ = v___x_3004_;
goto v___jp_2911_;
}
else
{
if (v___y_2989_ == 0)
{
v___y_2912_ = v___y_2984_;
v___y_2913_ = v___y_2992_;
v___y_2914_ = v___y_2995_;
v___y_2915_ = v___y_2996_;
v___y_2916_ = v___y_2999_;
v___y_2917_ = v___y_2997_;
v___y_2918_ = v___y_2994_;
v___y_2919_ = v___y_2989_;
v___y_2920_ = v___y_2990_;
v___y_2921_ = v___y_2993_;
v___y_2922_ = v___y_2985_;
v___y_2923_ = v___y_2998_;
v___y_2924_ = v___y_2988_;
v___y_2925_ = v_stxForExecution_2991_;
v___y_2926_ = v_a_3001_;
v___y_2927_ = v___y_2989_;
goto v___jp_2911_;
}
else
{
lean_object* v_ref_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_ref_3005_ = lean_ctor_get(v___y_2998_, 5);
v___x_3006_ = 0;
v___x_3007_ = l_Lean_SourceInfo_fromRef(v_ref_3005_, v___x_3006_);
v___x_3008_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3009_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3008_);
v___x_3010_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3014_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2990_) == 1)
{
lean_object* v_val_3015_; lean_object* v___x_3016_; 
v_val_3015_ = lean_ctor_get(v___y_2990_, 0);
lean_inc(v_val_3015_);
lean_dec_ref(v___y_2990_);
v___x_3016_ = l_Array_mkArray1___redArg(v_val_3015_);
v___y_2883_ = v___y_2984_;
v___y_2884_ = v___y_2992_;
v___y_2885_ = v___y_2995_;
v___y_2886_ = v___y_2996_;
v___y_2887_ = v___y_2999_;
v___y_2888_ = v___y_2997_;
v___y_2889_ = v___x_3014_;
v___y_2890_ = v___x_3012_;
v___y_2891_ = v___y_2994_;
v___y_2892_ = v___y_2989_;
v___y_2893_ = v___y_2993_;
v___y_2894_ = v___x_3013_;
v___y_2895_ = v___x_3009_;
v___y_2896_ = v___y_2985_;
v___y_2897_ = v___y_2998_;
v___y_2898_ = v___x_3007_;
v___y_2899_ = v___y_2988_;
v___y_2900_ = v_stxForExecution_2991_;
v___y_2901_ = v_a_3001_;
v___y_2902_ = v___x_3016_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_3017_; 
lean_dec(v___y_2990_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2883_ = v___y_2984_;
v___y_2884_ = v___y_2992_;
v___y_2885_ = v___y_2995_;
v___y_2886_ = v___y_2996_;
v___y_2887_ = v___y_2999_;
v___y_2888_ = v___y_2997_;
v___y_2889_ = v___x_3014_;
v___y_2890_ = v___x_3012_;
v___y_2891_ = v___y_2994_;
v___y_2892_ = v___y_2989_;
v___y_2893_ = v___y_2993_;
v___y_2894_ = v___x_3013_;
v___y_2895_ = v___x_3009_;
v___y_2896_ = v___y_2985_;
v___y_2897_ = v___y_2998_;
v___y_2898_ = v___x_3007_;
v___y_2899_ = v___y_2988_;
v___y_2900_ = v_stxForExecution_2991_;
v___y_2901_ = v_a_3001_;
v___y_2902_ = v___x_3017_;
goto v___jp_2882_;
}
}
}
}
}
v___jp_3018_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_inc_ref_n(v___y_3030_, 2);
v___x_3041_ = l_Array_append___redArg(v___y_3030_, v___y_3040_);
lean_dec_ref(v___y_3040_);
lean_inc_n(v___y_3022_, 2);
lean_inc_n(v___y_3028_, 2);
v___x_3042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3028_);
lean_ctor_set(v___x_3042_, 1, v___y_3022_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___y_3028_);
lean_ctor_set(v___x_3043_, 1, v___y_3022_);
lean_ctor_set(v___x_3043_, 2, v___y_3030_);
lean_inc(v___y_3036_);
v___x_3044_ = l_Lean_Syntax_node5(v___y_3028_, v___y_3033_, v___y_3020_, v___y_3036_, v___y_3023_, v___x_3042_, v___x_3043_);
v___y_2984_ = v___y_3019_;
v___y_2985_ = v___y_3032_;
v___y_2986_ = v___y_3036_;
v___y_2987_ = v___y_3037_;
v___y_2988_ = v___y_3038_;
v___y_2989_ = v___y_3025_;
v___y_2990_ = v___y_3026_;
v_stxForExecution_2991_ = v___x_3044_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3029_;
v___y_2994_ = v___y_3021_;
v___y_2995_ = v___y_3034_;
v___y_2996_ = v___y_3035_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3039_;
v___y_2999_ = v___y_3024_;
goto v___jp_2983_;
}
v___jp_3045_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_inc_ref(v___y_3056_);
v___x_3067_ = l_Array_append___redArg(v___y_3056_, v___y_3066_);
lean_dec_ref(v___y_3066_);
lean_inc(v___y_3049_);
lean_inc(v___y_3054_);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3054_);
lean_ctor_set(v___x_3068_, 1, v___y_3049_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
if (lean_obj_tag(v___y_3061_) == 1)
{
lean_object* v_val_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_val_3069_ = lean_ctor_get(v___y_3061_, 0);
v___x_3070_ = l_Lean_SourceInfo_fromRef(v_val_3069_, v___x_2514_);
v___x_3071_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = l_Array_mkArray1___redArg(v___x_3072_);
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___x_3068_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3061_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___y_3058_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___x_3073_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___x_3068_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3061_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___y_3058_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___x_3074_;
goto v___jp_3018_;
}
}
v___jp_3075_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref_n(v___y_3080_, 2);
v___x_3098_ = l_Array_append___redArg(v___y_3080_, v___y_3097_);
lean_dec_ref(v___y_3097_);
lean_inc_n(v___y_3088_, 3);
lean_inc_n(v___y_3078_, 5);
v___x_3099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3099_, 0, v___y_3078_);
lean_ctor_set(v___x_3099_, 1, v___y_3088_);
lean_ctor_set(v___x_3099_, 2, v___x_3098_);
v___x_3100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___y_3078_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3103_ = l_Lean_Syntax_SepArray_ofElems(v___x_3102_, v___y_3093_);
v___x_3104_ = l_Array_append___redArg(v___y_3080_, v___x_3103_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3078_);
lean_ctor_set(v___x_3105_, 1, v___y_3088_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___y_3078_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Lean_Syntax_node3(v___y_3078_, v___y_3088_, v___x_3101_, v___x_3105_, v___x_3107_);
lean_inc(v___y_3092_);
v___x_3109_ = l_Lean_Syntax_node5(v___y_3078_, v___y_3095_, v___y_3077_, v___y_3092_, v___y_3085_, v___x_3099_, v___x_3108_);
v___y_2984_ = v___y_3076_;
v___y_2985_ = v___y_3089_;
v___y_2986_ = v___y_3092_;
v___y_2987_ = v___y_3093_;
v___y_2988_ = v___y_3094_;
v___y_2989_ = v___y_3082_;
v___y_2990_ = v___y_3083_;
v_stxForExecution_2991_ = v___x_3109_;
v___y_2992_ = v___y_3084_;
v___y_2993_ = v___y_3086_;
v___y_2994_ = v___y_3079_;
v___y_2995_ = v___y_3090_;
v___y_2996_ = v___y_3091_;
v___y_2997_ = v___y_3087_;
v___y_2998_ = v___y_3096_;
v___y_2999_ = v___y_3081_;
goto v___jp_2983_;
}
v___jp_3110_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_inc_ref(v___y_3115_);
v___x_3132_ = l_Array_append___redArg(v___y_3115_, v___y_3131_);
lean_dec_ref(v___y_3131_);
lean_inc(v___y_3122_);
lean_inc(v___y_3113_);
v___x_3133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3133_, 0, v___y_3113_);
lean_ctor_set(v___x_3133_, 1, v___y_3122_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
if (lean_obj_tag(v___y_3125_) == 1)
{
lean_object* v_val_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_val_3134_ = lean_ctor_get(v___y_3125_, 0);
v___x_3135_ = l_Lean_SourceInfo_fromRef(v_val_3134_, v___x_2514_);
v___x_3136_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Array_mkArray1___redArg(v___x_3137_);
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3112_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___x_3133_;
v___y_3086_ = v___y_3120_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3122_;
v___y_3089_ = v___y_3125_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3123_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3128_;
v___y_3095_ = v___y_3129_;
v___y_3096_ = v___y_3130_;
v___y_3097_ = v___x_3138_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3112_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___x_3133_;
v___y_3086_ = v___y_3120_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3122_;
v___y_3089_ = v___y_3125_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3123_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3128_;
v___y_3095_ = v___y_3129_;
v___y_3096_ = v___y_3130_;
v___y_3097_ = v___x_3139_;
goto v___jp_3075_;
}
}
v___jp_3140_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_inc_ref_n(v___y_3151_, 2);
v___x_3163_ = l_Array_append___redArg(v___y_3151_, v___y_3162_);
lean_dec_ref(v___y_3162_);
lean_inc_n(v___y_3149_, 3);
lean_inc_n(v___y_3145_, 5);
v___x_3164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3164_, 0, v___y_3145_);
lean_ctor_set(v___x_3164_, 1, v___y_3149_);
lean_ctor_set(v___x_3164_, 2, v___x_3163_);
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3145_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3168_ = l_Lean_Syntax_SepArray_ofElems(v___x_3167_, v___y_3159_);
v___x_3169_ = l_Array_append___redArg(v___y_3151_, v___x_3168_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3170_, 0, v___y_3145_);
lean_ctor_set(v___x_3170_, 1, v___y_3149_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
v___x_3171_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___y_3145_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node3(v___y_3145_, v___y_3149_, v___x_3166_, v___x_3170_, v___x_3172_);
lean_inc(v___y_3158_);
v___x_3174_ = l_Lean_Syntax_node5(v___y_3145_, v___y_3142_, v___y_3144_, v___y_3158_, v___y_3154_, v___x_3164_, v___x_3173_);
v___y_2984_ = v___y_3141_;
v___y_2985_ = v___y_3155_;
v___y_2986_ = v___y_3158_;
v___y_2987_ = v___y_3159_;
v___y_2988_ = v___y_3160_;
v___y_2989_ = v___y_3147_;
v___y_2990_ = v___y_3148_;
v_stxForExecution_2991_ = v___x_3174_;
v___y_2992_ = v___y_3150_;
v___y_2993_ = v___y_3152_;
v___y_2994_ = v___y_3143_;
v___y_2995_ = v___y_3156_;
v___y_2996_ = v___y_3157_;
v___y_2997_ = v___y_3153_;
v___y_2998_ = v___y_3161_;
v___y_2999_ = v___y_3146_;
goto v___jp_2983_;
}
v___jp_3175_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
lean_inc_ref(v___y_3186_);
v___x_3197_ = l_Array_append___redArg(v___y_3186_, v___y_3196_);
lean_dec_ref(v___y_3196_);
lean_inc(v___y_3183_);
lean_inc(v___y_3180_);
v___x_3198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3180_);
lean_ctor_set(v___x_3198_, 1, v___y_3183_);
lean_ctor_set(v___x_3198_, 2, v___x_3197_);
if (lean_obj_tag(v___y_3191_) == 1)
{
lean_object* v_val_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_val_3199_ = lean_ctor_get(v___y_3191_, 0);
v___x_3200_ = l_Lean_SourceInfo_fromRef(v_val_3199_, v___x_2514_);
v___x_3201_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3200_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = l_Array_mkArray1___redArg(v___x_3202_);
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3182_;
v___y_3148_ = v___y_3184_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___x_3198_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3190_;
v___y_3157_ = v___y_3189_;
v___y_3158_ = v___y_3192_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___x_3203_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3204_; 
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3182_;
v___y_3148_ = v___y_3184_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___x_3198_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3190_;
v___y_3157_ = v___y_3189_;
v___y_3158_ = v___y_3192_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___x_3204_;
goto v___jp_3140_;
}
}
v___jp_3205_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_inc_ref_n(v___y_3207_, 2);
v___x_3228_ = l_Array_append___redArg(v___y_3207_, v___y_3227_);
lean_dec_ref(v___y_3227_);
lean_inc_n(v___y_3215_, 2);
lean_inc_n(v___y_3210_, 2);
v___x_3229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___y_3210_);
lean_ctor_set(v___x_3229_, 1, v___y_3215_);
lean_ctor_set(v___x_3229_, 2, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___y_3210_);
lean_ctor_set(v___x_3230_, 1, v___y_3215_);
lean_ctor_set(v___x_3230_, 2, v___y_3207_);
lean_inc(v___y_3222_);
v___x_3231_ = l_Lean_Syntax_node5(v___y_3210_, v___y_3209_, v___y_3225_, v___y_3222_, v___y_3217_, v___x_3229_, v___x_3230_);
v___y_2984_ = v___y_3206_;
v___y_2985_ = v___y_3219_;
v___y_2986_ = v___y_3222_;
v___y_2987_ = v___y_3223_;
v___y_2988_ = v___y_3224_;
v___y_2989_ = v___y_3212_;
v___y_2990_ = v___y_3213_;
v_stxForExecution_2991_ = v___x_3231_;
v___y_2992_ = v___y_3214_;
v___y_2993_ = v___y_3216_;
v___y_2994_ = v___y_3208_;
v___y_2995_ = v___y_3220_;
v___y_2996_ = v___y_3221_;
v___y_2997_ = v___y_3218_;
v___y_2998_ = v___y_3226_;
v___y_2999_ = v___y_3211_;
goto v___jp_2983_;
}
v___jp_3232_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_inc_ref(v___y_3234_);
v___x_3254_ = l_Array_append___redArg(v___y_3234_, v___y_3253_);
lean_dec_ref(v___y_3253_);
lean_inc(v___y_3242_);
lean_inc(v___y_3237_);
v___x_3255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3255_, 0, v___y_3237_);
lean_ctor_set(v___x_3255_, 1, v___y_3242_);
lean_ctor_set(v___x_3255_, 2, v___x_3254_);
if (lean_obj_tag(v___y_3247_) == 1)
{
lean_object* v_val_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_val_3256_ = lean_ctor_get(v___y_3247_, 0);
v___x_3257_ = l_Lean_SourceInfo_fromRef(v_val_3256_, v___x_2514_);
v___x_3258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Array_mkArray1___redArg(v___x_3259_);
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3255_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3245_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___y_3249_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3250_;
v___y_3226_ = v___y_3252_;
v___y_3227_ = v___x_3260_;
goto v___jp_3205_;
}
else
{
lean_object* v___x_3261_; 
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3255_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3245_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___y_3249_;
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3250_;
v___y_3226_ = v___y_3252_;
v___y_3227_ = v___x_3261_;
goto v___jp_3205_;
}
}
v___jp_3262_:
{
lean_object* v_ref_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_ref_3279_ = lean_ctor_get(v___y_3277_, 5);
v___x_3280_ = l_Lean_SourceInfo_fromRef(v_ref_3279_, v___y_3278_);
v___x_3281_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3282_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3281_);
v___x_3283_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_3284_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3287_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3267_) == 1)
{
lean_object* v_val_3288_; lean_object* v___x_3289_; 
v_val_3288_ = lean_ctor_get(v___y_3267_, 0);
lean_inc(v_val_3288_);
v___x_3289_ = l_Array_mkArray1___redArg(v_val_3288_);
v___y_3046_ = v___y_3263_;
v___y_3047_ = v___x_3285_;
v___y_3048_ = v___y_3264_;
v___y_3049_ = v___x_3286_;
v___y_3050_ = v___y_3265_;
v___y_3051_ = v___y_3266_;
v___y_3052_ = v___y_3267_;
v___y_3053_ = v___y_3268_;
v___y_3054_ = v___x_3280_;
v___y_3055_ = v___y_3269_;
v___y_3056_ = v___x_3287_;
v___y_3057_ = v___y_3270_;
v___y_3058_ = v___y_3271_;
v___y_3059_ = v___y_3272_;
v___y_3060_ = v___x_3282_;
v___y_3061_ = v___y_3273_;
v___y_3062_ = v___y_3274_;
v___y_3063_ = v___y_3275_;
v___y_3064_ = v___y_3276_;
v___y_3065_ = v___y_3277_;
v___y_3066_ = v___x_3289_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3290_; 
v___x_3290_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3046_ = v___y_3263_;
v___y_3047_ = v___x_3285_;
v___y_3048_ = v___y_3264_;
v___y_3049_ = v___x_3286_;
v___y_3050_ = v___y_3265_;
v___y_3051_ = v___y_3266_;
v___y_3052_ = v___y_3267_;
v___y_3053_ = v___y_3268_;
v___y_3054_ = v___x_3280_;
v___y_3055_ = v___y_3269_;
v___y_3056_ = v___x_3287_;
v___y_3057_ = v___y_3270_;
v___y_3058_ = v___y_3271_;
v___y_3059_ = v___y_3272_;
v___y_3060_ = v___x_3282_;
v___y_3061_ = v___y_3273_;
v___y_3062_ = v___y_3274_;
v___y_3063_ = v___y_3275_;
v___y_3064_ = v___y_3276_;
v___y_3065_ = v___y_3277_;
v___y_3066_ = v___x_3290_;
goto v___jp_3045_;
}
}
v___jp_3291_:
{
if (v___y_3308_ == 0)
{
lean_object* v_ref_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_ref_3309_ = lean_ctor_get(v___y_3307_, 5);
v___x_3310_ = l_Lean_SourceInfo_fromRef(v_ref_3309_, v___y_3308_);
v___x_3311_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3312_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3311_);
v___x_3313_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3317_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3297_) == 1)
{
lean_object* v_val_3318_; lean_object* v___x_3319_; 
v_val_3318_ = lean_ctor_get(v___y_3297_, 0);
lean_inc(v_val_3318_);
v___x_3319_ = l_Array_mkArray1___redArg(v_val_3318_);
v___y_3111_ = v___y_3292_;
v___y_3112_ = v___x_3315_;
v___y_3113_ = v___x_3310_;
v___y_3114_ = v___y_3293_;
v___y_3115_ = v___x_3317_;
v___y_3116_ = v___y_3295_;
v___y_3117_ = v___y_3296_;
v___y_3118_ = v___y_3297_;
v___y_3119_ = v___y_3298_;
v___y_3120_ = v___y_3299_;
v___y_3121_ = v___y_3300_;
v___y_3122_ = v___x_3316_;
v___y_3123_ = v___y_3301_;
v___y_3124_ = v___y_3302_;
v___y_3125_ = v___y_3303_;
v___y_3126_ = v___y_3304_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3306_;
v___y_3129_ = v___x_3312_;
v___y_3130_ = v___y_3307_;
v___y_3131_ = v___x_3319_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3111_ = v___y_3292_;
v___y_3112_ = v___x_3315_;
v___y_3113_ = v___x_3310_;
v___y_3114_ = v___y_3293_;
v___y_3115_ = v___x_3317_;
v___y_3116_ = v___y_3295_;
v___y_3117_ = v___y_3296_;
v___y_3118_ = v___y_3297_;
v___y_3119_ = v___y_3298_;
v___y_3120_ = v___y_3299_;
v___y_3121_ = v___y_3300_;
v___y_3122_ = v___x_3316_;
v___y_3123_ = v___y_3301_;
v___y_3124_ = v___y_3302_;
v___y_3125_ = v___y_3303_;
v___y_3126_ = v___y_3304_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3306_;
v___y_3129_ = v___x_3312_;
v___y_3130_ = v___y_3307_;
v___y_3131_ = v___x_3320_;
goto v___jp_3110_;
}
}
else
{
lean_object* v_ref_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_ref_3321_ = lean_ctor_get(v___y_3307_, 5);
v___x_3322_ = l_Lean_SourceInfo_fromRef(v_ref_3321_, v___y_3294_);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3324_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3323_);
v___x_3325_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3329_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3297_) == 1)
{
lean_object* v_val_3330_; lean_object* v___x_3331_; 
v_val_3330_ = lean_ctor_get(v___y_3297_, 0);
lean_inc(v_val_3330_);
v___x_3331_ = l_Array_mkArray1___redArg(v_val_3330_);
v___y_3176_ = v___y_3292_;
v___y_3177_ = v___x_3324_;
v___y_3178_ = v___y_3293_;
v___y_3179_ = v___x_3327_;
v___y_3180_ = v___x_3322_;
v___y_3181_ = v___y_3295_;
v___y_3182_ = v___y_3296_;
v___y_3183_ = v___x_3328_;
v___y_3184_ = v___y_3297_;
v___y_3185_ = v___y_3298_;
v___y_3186_ = v___x_3329_;
v___y_3187_ = v___y_3299_;
v___y_3188_ = v___y_3300_;
v___y_3189_ = v___y_3301_;
v___y_3190_ = v___y_3302_;
v___y_3191_ = v___y_3303_;
v___y_3192_ = v___y_3304_;
v___y_3193_ = v___y_3305_;
v___y_3194_ = v___y_3306_;
v___y_3195_ = v___y_3307_;
v___y_3196_ = v___x_3331_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3176_ = v___y_3292_;
v___y_3177_ = v___x_3324_;
v___y_3178_ = v___y_3293_;
v___y_3179_ = v___x_3327_;
v___y_3180_ = v___x_3322_;
v___y_3181_ = v___y_3295_;
v___y_3182_ = v___y_3296_;
v___y_3183_ = v___x_3328_;
v___y_3184_ = v___y_3297_;
v___y_3185_ = v___y_3298_;
v___y_3186_ = v___x_3329_;
v___y_3187_ = v___y_3299_;
v___y_3188_ = v___y_3300_;
v___y_3189_ = v___y_3301_;
v___y_3190_ = v___y_3302_;
v___y_3191_ = v___y_3303_;
v___y_3192_ = v___y_3304_;
v___y_3193_ = v___y_3305_;
v___y_3194_ = v___y_3306_;
v___y_3195_ = v___y_3307_;
v___y_3196_ = v___x_3332_;
goto v___jp_3175_;
}
}
}
v___jp_3333_:
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = lean_array_get_size(v_argsArray_3340_);
v___x_3350_ = lean_nat_dec_eq(v___x_3349_, v___x_2529_);
if (v___x_3350_ == 0)
{
if (lean_obj_tag(v___y_3337_) == 0)
{
v___y_3292_ = v___y_3334_;
v___y_3293_ = v___y_3343_;
v___y_3294_ = v___x_3350_;
v___y_3295_ = v___y_3348_;
v___y_3296_ = v___y_3338_;
v___y_3297_ = v___y_3339_;
v___y_3298_ = v___y_3341_;
v___y_3299_ = v___y_3342_;
v___y_3300_ = v___y_3346_;
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___y_3344_;
v___y_3303_ = v___y_3335_;
v___y_3304_ = v___y_3336_;
v___y_3305_ = v_argsArray_3340_;
v___y_3306_ = v___y_3337_;
v___y_3307_ = v___y_3347_;
v___y_3308_ = v___x_3350_;
goto v___jp_3291_;
}
else
{
v___y_3292_ = v___y_3334_;
v___y_3293_ = v___y_3343_;
v___y_3294_ = v___x_3350_;
v___y_3295_ = v___y_3348_;
v___y_3296_ = v___y_3338_;
v___y_3297_ = v___y_3339_;
v___y_3298_ = v___y_3341_;
v___y_3299_ = v___y_3342_;
v___y_3300_ = v___y_3346_;
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___y_3344_;
v___y_3303_ = v___y_3335_;
v___y_3304_ = v___y_3336_;
v___y_3305_ = v_argsArray_3340_;
v___y_3306_ = v___y_3337_;
v___y_3307_ = v___y_3347_;
v___y_3308_ = v___y_3338_;
goto v___jp_3291_;
}
}
else
{
if (lean_obj_tag(v___y_3337_) == 0)
{
uint8_t v___x_3351_; 
v___x_3351_ = 0;
v___y_3263_ = v___y_3334_;
v___y_3264_ = v___y_3343_;
v___y_3265_ = v___y_3348_;
v___y_3266_ = v___y_3338_;
v___y_3267_ = v___y_3339_;
v___y_3268_ = v___y_3341_;
v___y_3269_ = v___y_3342_;
v___y_3270_ = v___y_3346_;
v___y_3271_ = v___y_3345_;
v___y_3272_ = v___y_3344_;
v___y_3273_ = v___y_3335_;
v___y_3274_ = v___y_3336_;
v___y_3275_ = v_argsArray_3340_;
v___y_3276_ = v___y_3337_;
v___y_3277_ = v___y_3347_;
v___y_3278_ = v___x_3351_;
goto v___jp_3262_;
}
else
{
if (v___y_3338_ == 0)
{
v___y_3263_ = v___y_3334_;
v___y_3264_ = v___y_3343_;
v___y_3265_ = v___y_3348_;
v___y_3266_ = v___y_3338_;
v___y_3267_ = v___y_3339_;
v___y_3268_ = v___y_3341_;
v___y_3269_ = v___y_3342_;
v___y_3270_ = v___y_3346_;
v___y_3271_ = v___y_3345_;
v___y_3272_ = v___y_3344_;
v___y_3273_ = v___y_3335_;
v___y_3274_ = v___y_3336_;
v___y_3275_ = v_argsArray_3340_;
v___y_3276_ = v___y_3337_;
v___y_3277_ = v___y_3347_;
v___y_3278_ = v___y_3338_;
goto v___jp_3262_;
}
else
{
lean_object* v_ref_3352_; uint8_t v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_ref_3352_ = lean_ctor_get(v___y_3347_, 5);
v___x_3353_ = 0;
v___x_3354_ = l_Lean_SourceInfo_fromRef(v_ref_3352_, v___x_3353_);
v___x_3355_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3356_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3355_);
v___x_3357_ = l_Lean_SourceInfo_fromRef(v_tk_2530_, v___x_2514_);
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3361_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3339_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3363_; 
v_val_3362_ = lean_ctor_get(v___y_3339_, 0);
lean_inc(v_val_3362_);
v___x_3363_ = l_Array_mkArray1___redArg(v_val_3362_);
v___y_3233_ = v___y_3334_;
v___y_3234_ = v___x_3361_;
v___y_3235_ = v___y_3343_;
v___y_3236_ = v___x_3356_;
v___y_3237_ = v___x_3354_;
v___y_3238_ = v___y_3348_;
v___y_3239_ = v___y_3338_;
v___y_3240_ = v___y_3339_;
v___y_3241_ = v___y_3341_;
v___y_3242_ = v___x_3360_;
v___y_3243_ = v___y_3342_;
v___y_3244_ = v___y_3346_;
v___y_3245_ = v___y_3345_;
v___y_3246_ = v___y_3344_;
v___y_3247_ = v___y_3335_;
v___y_3248_ = v___y_3336_;
v___y_3249_ = v_argsArray_3340_;
v___y_3250_ = v___x_3359_;
v___y_3251_ = v___y_3337_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___x_3363_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3233_ = v___y_3334_;
v___y_3234_ = v___x_3361_;
v___y_3235_ = v___y_3343_;
v___y_3236_ = v___x_3356_;
v___y_3237_ = v___x_3354_;
v___y_3238_ = v___y_3348_;
v___y_3239_ = v___y_3338_;
v___y_3240_ = v___y_3339_;
v___y_3241_ = v___y_3341_;
v___y_3242_ = v___x_3360_;
v___y_3243_ = v___y_3342_;
v___y_3244_ = v___y_3346_;
v___y_3245_ = v___y_3345_;
v___y_3246_ = v___y_3344_;
v___y_3247_ = v___y_3335_;
v___y_3248_ = v___y_3336_;
v___y_3249_ = v_argsArray_3340_;
v___y_3250_ = v___x_3359_;
v___y_3251_ = v___y_3337_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___x_3364_;
goto v___jp_3232_;
}
}
}
}
}
v___jp_3365_:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3369_, v___y_3377_, v___y_3379_, v___y_3366_, v___y_3375_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = l_Lean_LibrarySuggestions_select(v_a_3383_, v___y_3381_, v___y_3377_, v___y_3379_, v___y_3366_, v___y_3375_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; size_t v_sz_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
v_sz_3386_ = lean_array_size(v_a_3385_);
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3385_, v_sz_3386_, v___x_3387_, v___y_3380_, v___y_3368_, v___y_3369_, v___y_3373_, v___y_3370_, v___y_3377_, v___y_3379_, v___y_3366_, v___y_3375_);
lean_dec(v_a_3385_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref(v___x_3388_);
v___y_3334_ = v___y_3367_;
v___y_3335_ = v___y_3374_;
v___y_3336_ = v___y_3376_;
v___y_3337_ = v___y_3378_;
v___y_3338_ = v___y_3371_;
v___y_3339_ = v___y_3372_;
v_argsArray_3340_ = v_a_3389_;
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3373_;
v___y_3344_ = v___y_3370_;
v___y_3345_ = v___y_3377_;
v___y_3346_ = v___y_3379_;
v___y_3347_ = v___y_3366_;
v___y_3348_ = v___y_3375_;
goto v___jp_3333_;
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v___y_3378_);
lean_dec(v___y_3376_);
lean_dec(v___y_3374_);
lean_dec(v___y_3372_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v_a_3390_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3388_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3388_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3378_);
lean_dec(v___y_3376_);
lean_dec(v___y_3374_);
lean_dec(v___y_3372_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v_a_3398_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3384_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3384_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3378_);
lean_dec(v___y_3376_);
lean_dec(v___y_3374_);
lean_dec(v___y_3372_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v_a_3406_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3382_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3382_);
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
uint8_t v_suggestions_3431_; 
v_suggestions_3431_ = lean_ctor_get_uint8(v___y_3421_, sizeof(void*)*3 + 26);
if (v_suggestions_3431_ == 0)
{
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___f_2518_);
v___y_3334_ = v___y_3416_;
v___y_3335_ = v___y_3424_;
v___y_3336_ = v___y_3426_;
v___y_3337_ = v___y_3428_;
v___y_3338_ = v___y_3420_;
v___y_3339_ = v___y_3422_;
v_argsArray_3340_ = v___y_3430_;
v___y_3341_ = v___y_3417_;
v___y_3342_ = v___y_3418_;
v___y_3343_ = v___y_3423_;
v___y_3344_ = v___y_3419_;
v___y_3345_ = v___y_3427_;
v___y_3346_ = v___y_3429_;
v___y_3347_ = v___y_3415_;
v___y_3348_ = v___y_3425_;
goto v___jp_3333_;
}
else
{
lean_object* v_maxSuggestions_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_maxSuggestions_3432_ = lean_ctor_get(v___y_3421_, 2);
lean_inc(v_maxSuggestions_3432_);
lean_dec_ref(v___y_3421_);
v___x_3433_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3434_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3432_) == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_unsigned_to_nat(100u);
v___x_3436_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___x_3433_);
lean_ctor_set(v___x_3436_, 2, v___f_2518_);
lean_ctor_set(v___x_3436_, 3, v___x_3434_);
v___y_3366_ = v___y_3415_;
v___y_3367_ = v___y_3416_;
v___y_3368_ = v___y_3417_;
v___y_3369_ = v___y_3418_;
v___y_3370_ = v___y_3419_;
v___y_3371_ = v___y_3420_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3424_;
v___y_3375_ = v___y_3425_;
v___y_3376_ = v___y_3426_;
v___y_3377_ = v___y_3427_;
v___y_3378_ = v___y_3428_;
v___y_3379_ = v___y_3429_;
v___y_3380_ = v___y_3430_;
v___y_3381_ = v___x_3436_;
goto v___jp_3365_;
}
else
{
lean_object* v_val_3437_; lean_object* v___x_3438_; 
v_val_3437_ = lean_ctor_get(v_maxSuggestions_3432_, 0);
lean_inc(v_val_3437_);
lean_dec_ref(v_maxSuggestions_3432_);
v___x_3438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3438_, 0, v_val_3437_);
lean_ctor_set(v___x_3438_, 1, v___x_3433_);
lean_ctor_set(v___x_3438_, 2, v___f_2518_);
lean_ctor_set(v___x_3438_, 3, v___x_3434_);
v___y_3366_ = v___y_3415_;
v___y_3367_ = v___y_3416_;
v___y_3368_ = v___y_3417_;
v___y_3369_ = v___y_3418_;
v___y_3370_ = v___y_3419_;
v___y_3371_ = v___y_3420_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3424_;
v___y_3375_ = v___y_3425_;
v___y_3376_ = v___y_3426_;
v___y_3377_ = v___y_3427_;
v___y_3378_ = v___y_3428_;
v___y_3379_ = v___y_3429_;
v___y_3380_ = v___y_3430_;
v___y_3381_ = v___x_3438_;
goto v___jp_3365_;
}
}
}
v___jp_3439_:
{
uint8_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = 1;
lean_inc(v___y_3448_);
v___x_3455_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3448_, v___x_3454_, v___y_3441_, v___y_3446_, v___y_3442_, v___y_3450_, v___y_3452_, v___y_3440_, v___y_3449_);
if (lean_obj_tag(v___x_3455_) == 0)
{
if (lean_obj_tag(v___y_3444_) == 1)
{
lean_object* v_a_3456_; lean_object* v_val_3457_; lean_object* v___x_3458_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref(v___x_3455_);
v_val_3457_ = lean_ctor_get(v___y_3444_, 0);
lean_inc(v_val_3457_);
lean_dec_ref(v___y_3444_);
v___x_3458_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3457_);
lean_dec(v_val_3457_);
v___y_3415_ = v___y_3440_;
v___y_3416_ = v___x_3454_;
v___y_3417_ = v___y_3441_;
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3445_;
v___y_3421_ = v_a_3456_;
v___y_3422_ = v___y_3453_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3448_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___y_3451_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___x_3458_;
goto v___jp_3414_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3460_; 
lean_dec(v___y_3444_);
v_a_3459_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3455_);
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3415_ = v___y_3440_;
v___y_3416_ = v___x_3454_;
v___y_3417_ = v___y_3441_;
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3445_;
v___y_3421_ = v_a_3459_;
v___y_3422_ = v___y_3453_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3448_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___y_3451_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___x_3460_;
goto v___jp_3414_;
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v___y_3453_);
lean_dec(v___y_3451_);
lean_dec(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec(v___y_3444_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v_a_3461_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3455_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3455_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
v___jp_3469_:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Syntax_getOptional_x3f(v___y_3472_);
lean_dec(v___y_3472_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_box(0);
v___y_3440_ = v___y_3482_;
v___y_3441_ = v___y_3476_;
v___y_3442_ = v___y_3479_;
v___y_3443_ = v___y_3477_;
v___y_3444_ = v_args_3475_;
v___y_3445_ = v___y_3474_;
v___y_3446_ = v___y_3478_;
v___y_3447_ = v___y_3470_;
v___y_3448_ = v___y_3471_;
v___y_3449_ = v___y_3483_;
v___y_3450_ = v___y_3480_;
v___y_3451_ = v___y_3473_;
v___y_3452_ = v___y_3481_;
v___y_3453_ = v___x_3485_;
goto v___jp_3439_;
}
else
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_val_3486_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_val_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
v___y_3440_ = v___y_3482_;
v___y_3441_ = v___y_3476_;
v___y_3442_ = v___y_3479_;
v___y_3443_ = v___y_3477_;
v___y_3444_ = v_args_3475_;
v___y_3445_ = v___y_3474_;
v___y_3446_ = v___y_3478_;
v___y_3447_ = v___y_3470_;
v___y_3448_ = v___y_3471_;
v___y_3449_ = v___y_3483_;
v___y_3450_ = v___y_3480_;
v___y_3451_ = v___y_3473_;
v___y_3452_ = v___y_3481_;
v___y_3453_ = v___x_3491_;
goto v___jp_3439_;
}
}
}
}
v___jp_3495_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3510_ = lean_unsigned_to_nat(3u);
v___x_3511_ = l_Lean_Syntax_getArg(v___y_3497_, v___x_3510_);
lean_dec(v___y_3497_);
v___x_3512_ = l_Lean_Syntax_isNone(v___x_3511_);
if (v___x_3512_ == 0)
{
uint8_t v___x_3513_; 
lean_inc(v___x_3511_);
v___x_3513_ = l_Lean_Syntax_matchesNull(v___x_3511_, v___x_3494_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_dec(v___x_3511_);
lean_dec(v_o_3501_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec(v___y_3496_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3514_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3515_ = l_Lean_Syntax_getArg(v___x_3511_, v___x_2529_);
lean_dec(v___x_3511_);
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3517_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3516_);
lean_inc(v___x_3515_);
v___x_3518_ = l_Lean_Syntax_isOfKind(v___x_3515_, v___x_3517_);
lean_dec(v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec(v___x_3515_);
lean_dec(v_o_3501_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec(v___y_3496_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v_args_3521_; lean_object* v___x_3522_; 
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3515_, v___x_3494_);
lean_dec(v___x_3515_);
v_args_3521_ = l_Lean_Syntax_getArgs(v___x_3520_);
lean_dec(v___x_3520_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_args_3521_);
v___y_3470_ = v_o_3501_;
v___y_3471_ = v___y_3496_;
v___y_3472_ = v___y_3499_;
v___y_3473_ = v___y_3498_;
v___y_3474_ = v___y_3500_;
v_args_3475_ = v___x_3522_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
v___y_3478_ = v___y_3504_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
goto v___jp_3469_;
}
}
}
else
{
lean_object* v___x_3523_; 
lean_dec(v___x_3511_);
v___x_3523_ = lean_box(0);
v___y_3470_ = v_o_3501_;
v___y_3471_ = v___y_3496_;
v___y_3472_ = v___y_3499_;
v___y_3473_ = v___y_3498_;
v___y_3474_ = v___y_3500_;
v_args_3475_ = v___x_3523_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
v___y_3478_ = v___y_3504_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
goto v___jp_3469_;
}
}
v___jp_3524_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3534_ = lean_unsigned_to_nat(2u);
v___x_3535_ = l_Lean_Syntax_getArg(v_stx_2513_, v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3537_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3536_);
lean_inc(v___x_3535_);
v___x_3538_ = l_Lean_Syntax_isOfKind(v___x_3535_, v___x_3537_);
lean_dec(v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v___x_3535_);
lean_dec(v_bang_3525_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3539_;
}
else
{
lean_object* v_cfg_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v_cfg_3540_ = l_Lean_Syntax_getArg(v___x_3535_, v___x_2529_);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_3542_ = l_Lean_Name_mkStr4(v___x_2515_, v___x_2516_, v___x_2517_, v___x_3541_);
lean_inc(v_cfg_3540_);
v___x_3543_ = l_Lean_Syntax_isOfKind(v_cfg_3540_, v___x_3542_);
lean_dec(v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; 
lean_dec(v_cfg_3540_);
lean_dec(v___x_3535_);
lean_dec(v_bang_3525_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3545_ = l_Lean_Syntax_getArg(v___x_3535_, v___x_3494_);
v___x_3546_ = l_Lean_Syntax_getArg(v___x_3535_, v___x_3534_);
v___x_3547_ = l_Lean_Syntax_isNone(v___x_3546_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
lean_inc(v___x_3546_);
v___x_3548_ = l_Lean_Syntax_matchesNull(v___x_3546_, v___x_3494_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v___x_3546_);
lean_dec(v___x_3545_);
lean_dec(v_cfg_3540_);
lean_dec(v___x_3535_);
lean_dec(v_bang_3525_);
lean_dec(v_tk_2530_);
lean_dec_ref(v___f_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___x_2515_);
v___x_3549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3549_;
}
else
{
lean_object* v_o_3550_; lean_object* v___x_3551_; 
v_o_3550_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_2529_);
lean_dec(v___x_3546_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_o_3550_);
v___y_3496_ = v_cfg_3540_;
v___y_3497_ = v___x_3535_;
v___y_3498_ = v_bang_3525_;
v___y_3499_ = v___x_3545_;
v___y_3500_ = v___x_3543_;
v_o_3501_ = v___x_3551_;
v___y_3502_ = v___y_3526_;
v___y_3503_ = v___y_3527_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3552_; 
lean_dec(v___x_3546_);
v___x_3552_ = lean_box(0);
v___y_3496_ = v_cfg_3540_;
v___y_3497_ = v___x_3535_;
v___y_3498_ = v_bang_3525_;
v___y_3499_ = v___x_3545_;
v___y_3500_ = v___x_3543_;
v_o_3501_ = v___x_3552_;
v___y_3502_ = v___y_3526_;
v___y_3503_ = v___y_3527_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
goto v___jp_3495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3560_, lean_object* v_stx_3561_, lean_object* v___x_3562_, lean_object* v___x_3563_, lean_object* v___x_3564_, lean_object* v___x_3565_, lean_object* v___f_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
uint8_t v___x_39020__boxed_3576_; uint8_t v___x_39021__boxed_3577_; lean_object* v_res_3578_; 
v___x_39020__boxed_3576_ = lean_unbox(v___x_3560_);
v___x_39021__boxed_3577_ = lean_unbox(v___x_3562_);
v_res_3578_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39020__boxed_3576_, v_stx_3561_, v___x_39021__boxed_3577_, v___x_3563_, v___x_3564_, v___x_3565_, v___f_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v_stx_3561_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; uint8_t v___x_3600_; lean_object* v___f_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___y_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3598_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3585_);
v___x_3599_ = l_Lean_Syntax_isOfKind(v_stx_3585_, v___x_3598_);
v___x_3600_ = 1;
v___f_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3602_ = lean_box(v___x_3599_);
v___x_3603_ = lean_box(v___x_3600_);
v___y_3604_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3604_, 0, v___x_3602_);
lean_closure_set(v___y_3604_, 1, v_stx_3585_);
lean_closure_set(v___y_3604_, 2, v___x_3603_);
lean_closure_set(v___y_3604_, 3, v___x_3595_);
lean_closure_set(v___y_3604_, 4, v___x_3596_);
lean_closure_set(v___y_3604_, 5, v___x_3597_);
lean_closure_set(v___y_3604_, 6, v___f_3601_);
v___x_3605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3605_, 0, v___y_3604_);
v___x_3606_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3605_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3618_, lean_object* v_as_3619_, lean_object* v_as_x27_3620_, lean_object* v_b_3621_, lean_object* v_a_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3618_, v_as_x27_3620_, v_b_3621_, v___y_3629_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3633_, lean_object* v_as_3634_, lean_object* v_as_x27_3635_, lean_object* v_b_3636_, lean_object* v_a_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3633_, v_as_3634_, v_as_x27_3635_, v_b_3636_, v_a_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v_as_x27_3635_);
lean_dec(v_as_3634_);
lean_dec(v___x_3633_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3655_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3658_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3655_, v___x_3656_, v___x_3657_, v___x_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3689_ = l_Lean_addBuiltinDeclarationRanges(v___x_3687_, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3692_, lean_object* v_simprocs_3693_, lean_object* v_fvarIdsToSimp_3694_, uint8_t v_simplifyTarget_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v___x_3702_);
v___x_3704_ = lean_unsigned_to_nat(32u);
v___x_3705_ = lean_mk_empty_array_with_capacity(v___x_3704_);
lean_dec_ref(v___x_3705_);
v___x_3706_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3707_ = l_Lean_Meta_dsimpGoal(v_a_3703_, v_ctx_3692_, v_simprocs_3693_, v_simplifyTarget_3695_, v_fvarIdsToSimp_3694_, v___x_3706_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v_fst_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
v_fst_3709_ = lean_ctor_get(v_a_3708_, 0);
if (lean_obj_tag(v_fst_3709_) == 0)
{
lean_object* v_snd_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_snd_3710_ = lean_ctor_get(v_a_3708_, 1);
lean_inc(v_snd_3710_);
lean_dec(v_a_3708_);
v___x_3711_ = lean_box(0);
v___x_3712_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3711_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; 
v_unused_3720_ = lean_ctor_get(v___x_3712_, 0);
lean_dec(v_unused_3720_);
v___x_3714_ = v___x_3712_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v___x_3712_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v_snd_3710_);
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_snd_3710_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec(v_snd_3710_);
v_a_3721_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3712_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3712_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3755_; 
lean_inc_ref(v_fst_3709_);
v_snd_3729_ = lean_ctor_get(v_a_3708_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v_a_3708_, 0);
lean_dec(v_unused_3756_);
v___x_3731_ = v_a_3708_;
v_isShared_3732_ = v_isSharedCheck_3755_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_snd_3729_);
lean_dec(v_a_3708_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3755_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v_val_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
v_val_3733_ = lean_ctor_get(v_fst_3709_, 0);
lean_inc(v_val_3733_);
lean_dec_ref(v_fst_3709_);
v___x_3734_ = lean_box(0);
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 1);
lean_ctor_set(v___x_3731_, 1, v___x_3734_);
lean_ctor_set(v___x_3731_, 0, v_val_3733_);
v___x_3736_ = v___x_3731_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_val_3733_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3736_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; 
v_unused_3745_ = lean_ctor_get(v___x_3737_, 0);
lean_dec(v_unused_3745_);
v___x_3739_ = v___x_3737_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_dec(v___x_3737_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_snd_3729_);
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_snd_3729_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_snd_3729_);
v_a_3746_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3737_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3737_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
v_a_3757_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3707_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3707_);
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
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_fvarIdsToSimp_3694_);
lean_dec_ref(v_simprocs_3693_);
lean_dec_ref(v_ctx_3692_);
v_a_3765_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3702_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3702_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3773_, lean_object* v_simprocs_3774_, lean_object* v_fvarIdsToSimp_3775_, lean_object* v_simplifyTarget_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
uint8_t v_simplifyTarget_boxed_3783_; lean_object* v_res_3784_; 
v_simplifyTarget_boxed_3783_ = lean_unbox(v_simplifyTarget_3776_);
v_res_3784_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3773_, v_simprocs_3774_, v_fvarIdsToSimp_3775_, v_simplifyTarget_boxed_3783_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3785_, lean_object* v_simprocs_3786_, lean_object* v_fvarIdsToSimp_3787_, uint8_t v_simplifyTarget_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3785_, v_simprocs_3786_, v_fvarIdsToSimp_3787_, v_simplifyTarget_3788_, v_a_3790_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3799_, lean_object* v_simprocs_3800_, lean_object* v_fvarIdsToSimp_3801_, lean_object* v_simplifyTarget_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
uint8_t v_simplifyTarget_boxed_3812_; lean_object* v_res_3813_; 
v_simplifyTarget_boxed_3812_ = lean_unbox(v_simplifyTarget_3802_);
v_res_3813_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3799_, v_simprocs_3800_, v_fvarIdsToSimp_3801_, v_simplifyTarget_boxed_3812_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3814_, lean_object* v_simprocs_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3817_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3827_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = l_Lean_MVarId_getNondepPropHyps(v_a_3826_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref(v___x_3827_);
v___x_3829_ = 1;
v___x_3830_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3814_, v_simprocs_3815_, v_a_3828_, v___x_3829_, v___y_3817_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3830_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v_simprocs_3815_);
lean_dec_ref(v_ctx_3814_);
v_a_3831_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3827_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3827_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec_ref(v_simprocs_3815_);
lean_dec_ref(v_ctx_3814_);
v_a_3839_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3825_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3825_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3847_, lean_object* v_simprocs_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3847_, v_simprocs_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3859_, lean_object* v_ctx_3860_, lean_object* v_simprocs_3861_, uint8_t v_type_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3859_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3872_);
v___x_3874_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3860_, v_simprocs_3861_, v_a_3873_, v_type_3862_, v___y_3864_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
return v___x_3874_;
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec_ref(v_simprocs_3861_);
lean_dec_ref(v_ctx_3860_);
v_a_3875_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3872_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3872_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3883_, lean_object* v_ctx_3884_, lean_object* v_simprocs_3885_, lean_object* v_type_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
uint8_t v_type_635__boxed_3896_; lean_object* v_res_3897_; 
v_type_635__boxed_3896_ = lean_unbox(v_type_3886_);
v_res_3897_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3883_, v_ctx_3884_, v_simprocs_3885_, v_type_635__boxed_3896_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3898_, lean_object* v_simprocs_3899_, lean_object* v_loc_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
if (lean_obj_tag(v_loc_3900_) == 0)
{
lean_object* v___f_3910_; lean_object* v___x_3911_; 
v___f_3910_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3910_, 0, v_ctx_3898_);
lean_closure_set(v___f_3910_, 1, v_simprocs_3899_);
v___x_3911_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3910_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
return v___x_3911_;
}
else
{
lean_object* v_hypotheses_3912_; uint8_t v_type_3913_; lean_object* v___x_3914_; lean_object* v___f_3915_; lean_object* v___x_3916_; 
v_hypotheses_3912_ = lean_ctor_get(v_loc_3900_, 0);
lean_inc_ref(v_hypotheses_3912_);
v_type_3913_ = lean_ctor_get_uint8(v_loc_3900_, sizeof(void*)*1);
lean_dec_ref(v_loc_3900_);
v___x_3914_ = lean_box(v_type_3913_);
v___f_3915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3915_, 0, v_hypotheses_3912_);
lean_closure_set(v___f_3915_, 1, v_ctx_3898_);
lean_closure_set(v___f_3915_, 2, v_simprocs_3899_);
lean_closure_set(v___f_3915_, 3, v___x_3914_);
v___x_3916_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3915_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3917_, lean_object* v_simprocs_3918_, lean_object* v_loc_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3917_, v_simprocs_3918_, v_loc_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3934_, lean_object* v_stx_3935_, uint8_t v___x_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
if (v___x_3934_ == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_3949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v_tk_3951_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; uint8_t v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v_stx_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; uint8_t v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; uint8_t v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; uint8_t v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; uint8_t v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; uint8_t v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; uint8_t v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4305_; lean_object* v___y_4306_; uint8_t v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v_args_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___x_4331_; lean_object* v___y_4333_; uint8_t v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v_o_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v_bang_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_3950_ = lean_unsigned_to_nat(0u);
v_tk_3951_ = l_Lean_Syntax_getArg(v_stx_3935_, v___x_3950_);
v___x_4331_ = lean_unsigned_to_nat(1u);
v___x_4388_ = l_Lean_Syntax_getArg(v_stx_3935_, v___x_4331_);
v___x_4389_ = l_Lean_Syntax_isNone(v___x_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
lean_inc(v___x_4388_);
v___x_4390_ = l_Lean_Syntax_matchesNull(v___x_4388_, v___x_4331_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; 
lean_dec(v___x_4388_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4391_;
}
else
{
lean_object* v_bang_4392_; lean_object* v___x_4393_; 
v_bang_4392_ = l_Lean_Syntax_getArg(v___x_4388_, v___x_3950_);
lean_dec(v___x_4388_);
v___x_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4393_, 0, v_bang_4392_);
v_bang_4361_ = v___x_4393_;
v___y_4362_ = v___y_3940_;
v___y_4363_ = v___y_3941_;
v___y_4364_ = v___y_3942_;
v___y_4365_ = v___y_3943_;
v___y_4366_ = v___y_3944_;
v___y_4367_ = v___y_3945_;
v___y_4368_ = v___y_3946_;
v___y_4369_ = v___y_3947_;
goto v___jp_4360_;
}
}
else
{
lean_object* v___x_4394_; 
lean_dec(v___x_4388_);
v___x_4394_ = lean_box(0);
v_bang_4361_ = v___x_4394_;
v___y_4362_ = v___y_3940_;
v___y_4363_ = v___y_3941_;
v___y_4364_ = v___y_3942_;
v___y_4365_ = v___y_3943_;
v___y_4366_ = v___y_3944_;
v___y_4367_ = v___y_3945_;
v___y_4368_ = v___y_3946_;
v___y_4369_ = v___y_3947_;
goto v___jp_4360_;
}
v___jp_3952_:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3955_, v___y_3954_, v___y_3964_, v___y_3962_, v___y_3956_, v___y_3961_, v___y_3957_, v___y_3960_, v___y_3963_, v___y_3958_, v___y_3953_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v_usedTheorems_3967_; lean_object* v_diag_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4009_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
v_usedTheorems_3967_ = lean_ctor_get(v_a_3966_, 0);
v_diag_3968_ = lean_ctor_get(v_a_3966_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_a_3966_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3970_ = v_a_3966_;
v_isShared_3971_ = v_isSharedCheck_4009_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_diag_3968_);
lean_inc(v_usedTheorems_3967_);
lean_dec(v_a_3966_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4009_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3959_, v_usedTheorems_3967_, v___y_3960_, v___y_3963_, v___y_3958_, v___y_3953_);
lean_dec_ref(v_usedTheorems_3967_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v_ref_3974_; lean_object* v___x_3975_; lean_object* v___x_3977_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v_ref_3974_ = lean_ctor_get(v___y_3958_, 5);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v_a_3973_);
lean_ctor_set(v___x_3970_, 0, v___x_3975_);
v___x_3977_ = v___x_3970_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3975_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_a_3973_);
v___x_3977_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
lean_ctor_set(v___x_3979_, 2, v___x_3978_);
lean_ctor_set(v___x_3979_, 3, v___x_3978_);
lean_ctor_set(v___x_3979_, 4, v___x_3978_);
lean_ctor_set(v___x_3979_, 5, v___x_3978_);
lean_inc(v_ref_3974_);
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v_ref_3974_);
v___x_3981_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3982_ = 4;
v___x_3983_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3951_, v___x_3979_, v___x_3980_, v___x_3981_, v___x_3978_, v___x_3982_, v___y_3958_, v___y_3953_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v___x_3983_, 0);
lean_dec(v_unused_3991_);
v___x_3985_ = v___x_3983_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_dec(v___x_3983_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v_diag_3968_);
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_diag_3968_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec_ref(v_diag_3968_);
v_a_3992_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3983_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3983_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_del_object(v___x_3970_);
lean_dec_ref(v_diag_3968_);
lean_dec(v_tk_3951_);
v_a_4001_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3972_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3972_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v___y_3959_);
lean_dec(v_tk_3951_);
v_a_4010_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3965_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3965_);
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
if (lean_obj_tag(v___y_4029_) == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4032_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
lean_ctor_set_uint8(v___x_4032_, sizeof(void*)*1, v___x_3936_);
v___y_3953_ = v___y_4019_;
v___y_3954_ = v___y_4020_;
v___y_3955_ = v___y_4030_;
v___y_3956_ = v___y_4021_;
v___y_3957_ = v___y_4022_;
v___y_3958_ = v___y_4023_;
v___y_3959_ = v___y_4026_;
v___y_3960_ = v___y_4025_;
v___y_3961_ = v___y_4024_;
v___y_3962_ = v___y_4027_;
v___y_3963_ = v___y_4028_;
v___y_3964_ = v___x_4032_;
goto v___jp_3952_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4034_; 
v_val_4033_ = lean_ctor_get(v___y_4029_, 0);
lean_inc(v_val_4033_);
lean_dec_ref(v___y_4029_);
v___x_4034_ = l_Lean_Elab_Tactic_expandLocation(v_val_4033_);
lean_dec(v_val_4033_);
v___y_3953_ = v___y_4019_;
v___y_3954_ = v___y_4020_;
v___y_3955_ = v___y_4030_;
v___y_3956_ = v___y_4021_;
v___y_3957_ = v___y_4022_;
v___y_3958_ = v___y_4023_;
v___y_3959_ = v___y_4026_;
v___y_3960_ = v___y_4025_;
v___y_3961_ = v___y_4024_;
v___y_3962_ = v___y_4027_;
v___y_3963_ = v___y_4028_;
v___y_3964_ = v___x_4034_;
goto v___jp_3952_;
}
}
v___jp_4035_:
{
uint8_t v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4048_ = 0;
v___x_4049_ = 2;
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4051_ = lean_box(v___x_4048_);
v___x_4052_ = lean_box(v___x_4049_);
v___x_4053_ = lean_box(v___x_4048_);
lean_inc(v_stx_4039_);
v___x_4054_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4054_, 0, v_stx_4039_);
lean_closure_set(v___x_4054_, 1, v___x_4051_);
lean_closure_set(v___x_4054_, 2, v___x_4052_);
lean_closure_set(v___x_4054_, 3, v___x_4053_);
lean_closure_set(v___x_4054_, 4, v___x_4050_);
v___x_4055_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4054_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v___x_4055_);
if (lean_obj_tag(v___y_4037_) == 0)
{
lean_object* v_ctx_4057_; lean_object* v_simprocs_4058_; 
v_ctx_4057_ = lean_ctor_get(v_a_4056_, 0);
lean_inc_ref(v_ctx_4057_);
v_simprocs_4058_ = lean_ctor_get(v_a_4056_, 1);
lean_inc_ref(v_simprocs_4058_);
lean_dec(v_a_4056_);
v___y_4019_ = v___y_4047_;
v___y_4020_ = v_simprocs_4058_;
v___y_4021_ = v___y_4041_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4046_;
v___y_4024_ = v___y_4042_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v_stx_4039_;
v___y_4027_ = v___y_4040_;
v___y_4028_ = v___y_4045_;
v___y_4029_ = v___y_4038_;
v___y_4030_ = v_ctx_4057_;
goto v___jp_4018_;
}
else
{
lean_dec_ref(v___y_4037_);
if (v___y_4036_ == 0)
{
lean_object* v_ctx_4059_; lean_object* v_simprocs_4060_; 
v_ctx_4059_ = lean_ctor_get(v_a_4056_, 0);
lean_inc_ref(v_ctx_4059_);
v_simprocs_4060_ = lean_ctor_get(v_a_4056_, 1);
lean_inc_ref(v_simprocs_4060_);
lean_dec(v_a_4056_);
v___y_4019_ = v___y_4047_;
v___y_4020_ = v_simprocs_4060_;
v___y_4021_ = v___y_4041_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4046_;
v___y_4024_ = v___y_4042_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v_stx_4039_;
v___y_4027_ = v___y_4040_;
v___y_4028_ = v___y_4045_;
v___y_4029_ = v___y_4038_;
v___y_4030_ = v_ctx_4059_;
goto v___jp_4018_;
}
else
{
lean_object* v_ctx_4061_; lean_object* v_simprocs_4062_; lean_object* v___x_4063_; 
v_ctx_4061_ = lean_ctor_get(v_a_4056_, 0);
lean_inc_ref(v_ctx_4061_);
v_simprocs_4062_ = lean_ctor_get(v_a_4056_, 1);
lean_inc_ref(v_simprocs_4062_);
lean_dec(v_a_4056_);
v___x_4063_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4061_);
v___y_4019_ = v___y_4047_;
v___y_4020_ = v_simprocs_4062_;
v___y_4021_ = v___y_4041_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4046_;
v___y_4024_ = v___y_4042_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v_stx_4039_;
v___y_4027_ = v___y_4040_;
v___y_4028_ = v___y_4045_;
v___y_4029_ = v___y_4038_;
v___y_4030_ = v___x_4063_;
goto v___jp_4018_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_stx_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v_tk_3951_);
v_a_4064_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4055_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4055_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
v___jp_4072_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_inc_ref(v___y_4075_);
v___x_4094_ = l_Array_append___redArg(v___y_4075_, v___y_4093_);
lean_dec_ref(v___y_4093_);
lean_inc(v___y_4088_);
lean_inc(v___y_4080_);
v___x_4095_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4095_, 0, v___y_4080_);
lean_ctor_set(v___x_4095_, 1, v___y_4088_);
lean_ctor_set(v___x_4095_, 2, v___x_4094_);
v___x_4096_ = l_Lean_Syntax_node6(v___y_4080_, v___y_4083_, v___y_4078_, v___y_4079_, v___y_4081_, v___y_4074_, v___y_4084_, v___x_4095_);
v___y_4036_ = v___y_4077_;
v___y_4037_ = v___y_4092_;
v___y_4038_ = v___y_4091_;
v_stx_4039_ = v___x_4096_;
v___y_4040_ = v___y_4090_;
v___y_4041_ = v___y_4089_;
v___y_4042_ = v___y_4073_;
v___y_4043_ = v___y_4087_;
v___y_4044_ = v___y_4086_;
v___y_4045_ = v___y_4082_;
v___y_4046_ = v___y_4076_;
v___y_4047_ = v___y_4085_;
goto v___jp_4035_;
}
v___jp_4097_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_inc_ref(v___y_4100_);
v___x_4118_ = l_Array_append___redArg(v___y_4100_, v___y_4117_);
lean_dec_ref(v___y_4117_);
lean_inc(v___y_4112_);
lean_inc(v___y_4105_);
v___x_4119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4119_, 0, v___y_4105_);
lean_ctor_set(v___x_4119_, 1, v___y_4112_);
lean_ctor_set(v___x_4119_, 2, v___x_4118_);
if (lean_obj_tag(v___y_4116_) == 0)
{
lean_object* v___x_4120_; 
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___y_4100_;
v___y_4076_ = v___y_4101_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4106_;
v___y_4082_ = v___y_4107_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___x_4119_;
v___y_4085_ = v___y_4111_;
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___y_4109_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4113_;
v___y_4090_ = v___y_4114_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4115_;
v___y_4093_ = v___x_4120_;
goto v___jp_4072_;
}
else
{
lean_object* v_val_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_val_4121_ = lean_ctor_get(v___y_4116_, 0);
v___x_4122_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4121_);
v___x_4123_ = lean_array_push(v___x_4122_, v_val_4121_);
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___y_4100_;
v___y_4076_ = v___y_4101_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4106_;
v___y_4082_ = v___y_4107_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___x_4119_;
v___y_4085_ = v___y_4111_;
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___y_4109_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4113_;
v___y_4090_ = v___y_4114_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4115_;
v___y_4093_ = v___x_4123_;
goto v___jp_4072_;
}
}
v___jp_4124_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_inc_ref(v___y_4127_);
v___x_4145_ = l_Array_append___redArg(v___y_4127_, v___y_4144_);
lean_dec_ref(v___y_4144_);
lean_inc(v___y_4139_);
lean_inc(v___y_4132_);
v___x_4146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___y_4132_);
lean_ctor_set(v___x_4146_, 1, v___y_4139_);
lean_ctor_set(v___x_4146_, 2, v___x_4145_);
if (lean_obj_tag(v___y_4126_) == 1)
{
lean_object* v_val_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_val_4147_ = lean_ctor_get(v___y_4126_, 0);
lean_inc(v_val_4147_);
lean_dec_ref(v___y_4126_);
v___x_4148_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4132_, 3);
v___x_4149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___y_4132_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
lean_inc_ref(v___y_4127_);
v___x_4150_ = l_Array_append___redArg(v___y_4127_, v_val_4147_);
lean_dec(v_val_4147_);
lean_inc(v___y_4139_);
v___x_4151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4151_, 0, v___y_4132_);
lean_ctor_set(v___x_4151_, 1, v___y_4139_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___y_4132_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = l_Array_mkArray3___redArg(v___x_4149_, v___x_4151_, v___x_4153_);
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___x_4146_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___y_4133_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4138_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4140_;
v___y_4114_ = v___y_4141_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___x_4154_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4155_; 
lean_dec(v___y_4126_);
v___x_4155_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___x_4146_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___y_4133_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4138_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4140_;
v___y_4114_ = v___y_4141_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___x_4155_;
goto v___jp_4097_;
}
}
v___jp_4156_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_inc_ref(v___y_4160_);
v___x_4178_ = l_Array_append___redArg(v___y_4160_, v___y_4177_);
lean_dec_ref(v___y_4177_);
lean_inc(v___y_4167_);
lean_inc(v___y_4162_);
v___x_4179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4179_, 0, v___y_4162_);
lean_ctor_set(v___x_4179_, 1, v___y_4167_);
lean_ctor_set(v___x_4179_, 2, v___x_4178_);
v___x_4180_ = l_Lean_Syntax_node6(v___y_4162_, v___y_4163_, v___y_4166_, v___y_4165_, v___y_4168_, v___y_4158_, v___y_4164_, v___x_4179_);
v___y_4036_ = v___y_4161_;
v___y_4037_ = v___y_4176_;
v___y_4038_ = v___y_4175_;
v_stx_4039_ = v___x_4180_;
v___y_4040_ = v___y_4174_;
v___y_4041_ = v___y_4173_;
v___y_4042_ = v___y_4157_;
v___y_4043_ = v___y_4172_;
v___y_4044_ = v___y_4171_;
v___y_4045_ = v___y_4169_;
v___y_4046_ = v___y_4159_;
v___y_4047_ = v___y_4170_;
goto v___jp_4035_;
}
v___jp_4181_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_inc_ref(v___y_4185_);
v___x_4202_ = l_Array_append___redArg(v___y_4185_, v___y_4201_);
lean_dec_ref(v___y_4201_);
lean_inc(v___y_4191_);
lean_inc(v___y_4187_);
v___x_4203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4203_, 0, v___y_4187_);
lean_ctor_set(v___x_4203_, 1, v___y_4191_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
if (lean_obj_tag(v___y_4200_) == 0)
{
lean_object* v___x_4204_; 
v___x_4204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___y_4183_;
v___y_4159_ = v___y_4184_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___x_4203_;
v___y_4165_ = v___y_4189_;
v___y_4166_ = v___y_4190_;
v___y_4167_ = v___y_4191_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___y_4193_;
v___y_4170_ = v___y_4196_;
v___y_4171_ = v___y_4195_;
v___y_4172_ = v___y_4194_;
v___y_4173_ = v___y_4197_;
v___y_4174_ = v___y_4198_;
v___y_4175_ = v___y_4200_;
v___y_4176_ = v___y_4199_;
v___y_4177_ = v___x_4204_;
goto v___jp_4156_;
}
else
{
lean_object* v_val_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_val_4205_ = lean_ctor_get(v___y_4200_, 0);
v___x_4206_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4205_);
v___x_4207_ = lean_array_push(v___x_4206_, v_val_4205_);
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___y_4183_;
v___y_4159_ = v___y_4184_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___x_4203_;
v___y_4165_ = v___y_4189_;
v___y_4166_ = v___y_4190_;
v___y_4167_ = v___y_4191_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___y_4193_;
v___y_4170_ = v___y_4196_;
v___y_4171_ = v___y_4195_;
v___y_4172_ = v___y_4194_;
v___y_4173_ = v___y_4197_;
v___y_4174_ = v___y_4198_;
v___y_4175_ = v___y_4200_;
v___y_4176_ = v___y_4199_;
v___y_4177_ = v___x_4207_;
goto v___jp_4156_;
}
}
v___jp_4208_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
lean_inc_ref(v___y_4212_);
v___x_4229_ = l_Array_append___redArg(v___y_4212_, v___y_4228_);
lean_dec_ref(v___y_4228_);
lean_inc(v___y_4218_);
lean_inc(v___y_4214_);
v___x_4230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4230_, 0, v___y_4214_);
lean_ctor_set(v___x_4230_, 1, v___y_4218_);
lean_ctor_set(v___x_4230_, 2, v___x_4229_);
if (lean_obj_tag(v___y_4210_) == 1)
{
lean_object* v_val_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_val_4231_ = lean_ctor_get(v___y_4210_, 0);
lean_inc(v_val_4231_);
lean_dec_ref(v___y_4210_);
v___x_4232_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4214_, 3);
v___x_4233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___y_4214_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
lean_inc_ref(v___y_4212_);
v___x_4234_ = l_Array_append___redArg(v___y_4212_, v_val_4231_);
lean_dec(v_val_4231_);
lean_inc(v___y_4218_);
v___x_4235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4235_, 0, v___y_4214_);
lean_ctor_set(v___x_4235_, 1, v___y_4218_);
lean_ctor_set(v___x_4235_, 2, v___x_4234_);
v___x_4236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___y_4214_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = l_Array_mkArray3___redArg(v___x_4233_, v___x_4235_, v___x_4237_);
v___y_4182_ = v___y_4209_;
v___y_4183_ = v___x_4230_;
v___y_4184_ = v___y_4211_;
v___y_4185_ = v___y_4212_;
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___y_4216_;
v___y_4190_ = v___y_4217_;
v___y_4191_ = v___y_4218_;
v___y_4192_ = v___y_4219_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4223_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4221_;
v___y_4197_ = v___y_4224_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4227_;
v___y_4200_ = v___y_4226_;
v___y_4201_ = v___x_4238_;
goto v___jp_4181_;
}
else
{
lean_object* v___x_4239_; 
lean_dec(v___y_4210_);
v___x_4239_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4182_ = v___y_4209_;
v___y_4183_ = v___x_4230_;
v___y_4184_ = v___y_4211_;
v___y_4185_ = v___y_4212_;
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___y_4216_;
v___y_4190_ = v___y_4217_;
v___y_4191_ = v___y_4218_;
v___y_4192_ = v___y_4219_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4223_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4221_;
v___y_4197_ = v___y_4224_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4227_;
v___y_4200_ = v___y_4226_;
v___y_4201_ = v___x_4239_;
goto v___jp_4181_;
}
}
v___jp_4240_:
{
lean_object* v_ref_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_ref_4256_ = lean_ctor_get(v___y_4243_, 5);
v___x_4257_ = l_Lean_SourceInfo_fromRef(v_ref_4256_, v___y_4255_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4259_ = l_Lean_Name_mkStr4(v___x_3937_, v___x_3938_, v___x_3939_, v___x_4258_);
v___x_4260_ = l_Lean_SourceInfo_fromRef(v_tk_3951_, v___x_3936_);
v___x_4261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
lean_ctor_set(v___x_4261_, 1, v___x_4258_);
v___x_4262_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4263_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4257_);
v___x_4264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4257_);
lean_ctor_set(v___x_4264_, 1, v___x_4262_);
lean_ctor_set(v___x_4264_, 2, v___x_4263_);
if (lean_obj_tag(v___y_4247_) == 1)
{
lean_object* v_val_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_val_4265_ = lean_ctor_get(v___y_4247_, 0);
lean_inc(v_val_4265_);
lean_dec_ref(v___y_4247_);
v___x_4266_ = l_Lean_SourceInfo_fromRef(v_val_4265_, v___x_3936_);
lean_dec(v_val_4265_);
v___x_4267_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4266_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = l_Array_mkArray1___redArg(v___x_4268_);
v___y_4125_ = v___y_4241_;
v___y_4126_ = v___y_4242_;
v___y_4127_ = v___x_4263_;
v___y_4128_ = v___y_4243_;
v___y_4129_ = v___y_4244_;
v___y_4130_ = v___x_4261_;
v___y_4131_ = v___y_4245_;
v___y_4132_ = v___x_4257_;
v___y_4133_ = v___x_4264_;
v___y_4134_ = v___y_4246_;
v___y_4135_ = v___x_4259_;
v___y_4136_ = v___y_4248_;
v___y_4137_ = v___y_4249_;
v___y_4138_ = v___y_4250_;
v___y_4139_ = v___x_4262_;
v___y_4140_ = v___y_4251_;
v___y_4141_ = v___y_4252_;
v___y_4142_ = v___y_4254_;
v___y_4143_ = v___y_4253_;
v___y_4144_ = v___x_4269_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4270_; 
lean_dec(v___y_4247_);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4125_ = v___y_4241_;
v___y_4126_ = v___y_4242_;
v___y_4127_ = v___x_4263_;
v___y_4128_ = v___y_4243_;
v___y_4129_ = v___y_4244_;
v___y_4130_ = v___x_4261_;
v___y_4131_ = v___y_4245_;
v___y_4132_ = v___x_4257_;
v___y_4133_ = v___x_4264_;
v___y_4134_ = v___y_4246_;
v___y_4135_ = v___x_4259_;
v___y_4136_ = v___y_4248_;
v___y_4137_ = v___y_4249_;
v___y_4138_ = v___y_4250_;
v___y_4139_ = v___x_4262_;
v___y_4140_ = v___y_4251_;
v___y_4141_ = v___y_4252_;
v___y_4142_ = v___y_4254_;
v___y_4143_ = v___y_4253_;
v___y_4144_ = v___x_4270_;
goto v___jp_4124_;
}
}
v___jp_4271_:
{
if (lean_obj_tag(v___y_4284_) == 0)
{
uint8_t v___x_4286_; 
v___x_4286_ = 0;
v___y_4241_ = v___y_4272_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4274_;
v___y_4244_ = v___y_4275_;
v___y_4245_ = v___y_4276_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4283_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___x_4286_;
goto v___jp_4240_;
}
else
{
if (v___y_4275_ == 0)
{
v___y_4241_ = v___y_4272_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4274_;
v___y_4244_ = v___y_4275_;
v___y_4245_ = v___y_4276_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4283_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4275_;
goto v___jp_4240_;
}
else
{
lean_object* v_ref_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_ref_4287_ = lean_ctor_get(v___y_4274_, 5);
v___x_4288_ = 0;
v___x_4289_ = l_Lean_SourceInfo_fromRef(v_ref_4287_, v___x_4288_);
v___x_4290_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4291_ = l_Lean_Name_mkStr4(v___x_3937_, v___x_3938_, v___x_3939_, v___x_4290_);
v___x_4292_ = l_Lean_SourceInfo_fromRef(v_tk_3951_, v___x_3936_);
v___x_4293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4296_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4289_);
v___x_4297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4289_);
lean_ctor_set(v___x_4297_, 1, v___x_4295_);
lean_ctor_set(v___x_4297_, 2, v___x_4296_);
if (lean_obj_tag(v___y_4278_) == 1)
{
lean_object* v_val_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_val_4298_ = lean_ctor_get(v___y_4278_, 0);
lean_inc(v_val_4298_);
lean_dec_ref(v___y_4278_);
v___x_4299_ = l_Lean_SourceInfo_fromRef(v_val_4298_, v___x_3936_);
lean_dec(v_val_4298_);
v___x_4300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Array_mkArray1___redArg(v___x_4301_);
v___y_4209_ = v___y_4272_;
v___y_4210_ = v___y_4273_;
v___y_4211_ = v___y_4274_;
v___y_4212_ = v___x_4296_;
v___y_4213_ = v___y_4275_;
v___y_4214_ = v___x_4289_;
v___y_4215_ = v___x_4291_;
v___y_4216_ = v___y_4276_;
v___y_4217_ = v___x_4294_;
v___y_4218_ = v___x_4295_;
v___y_4219_ = v___x_4297_;
v___y_4220_ = v___y_4277_;
v___y_4221_ = v___y_4279_;
v___y_4222_ = v___y_4280_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4282_;
v___y_4225_ = v___y_4283_;
v___y_4226_ = v___y_4285_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___x_4302_;
goto v___jp_4208_;
}
else
{
lean_object* v___x_4303_; 
lean_dec(v___y_4278_);
v___x_4303_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4209_ = v___y_4272_;
v___y_4210_ = v___y_4273_;
v___y_4211_ = v___y_4274_;
v___y_4212_ = v___x_4296_;
v___y_4213_ = v___y_4275_;
v___y_4214_ = v___x_4289_;
v___y_4215_ = v___x_4291_;
v___y_4216_ = v___y_4276_;
v___y_4217_ = v___x_4294_;
v___y_4218_ = v___x_4295_;
v___y_4219_ = v___x_4297_;
v___y_4220_ = v___y_4277_;
v___y_4221_ = v___y_4279_;
v___y_4222_ = v___y_4280_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4282_;
v___y_4225_ = v___y_4283_;
v___y_4226_ = v___y_4285_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___x_4303_;
goto v___jp_4208_;
}
}
}
}
v___jp_4304_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = lean_unsigned_to_nat(3u);
v___x_4320_ = l_Lean_Syntax_getArg(v___y_4305_, v___x_4319_);
lean_dec(v___y_4305_);
v___x_4321_ = l_Lean_Syntax_getOptional_x3f(v___x_4320_);
lean_dec(v___x_4320_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v___x_4322_; 
v___x_4322_ = lean_box(0);
v___y_4272_ = v___y_4313_;
v___y_4273_ = v_args_4310_;
v___y_4274_ = v___y_4317_;
v___y_4275_ = v___y_4307_;
v___y_4276_ = v___y_4308_;
v___y_4277_ = v___y_4316_;
v___y_4278_ = v___y_4306_;
v___y_4279_ = v___y_4318_;
v___y_4280_ = v___y_4315_;
v___y_4281_ = v___y_4314_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4309_;
v___y_4285_ = v___x_4322_;
goto v___jp_4271_;
}
else
{
lean_object* v_val_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_val_4323_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4321_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_val_4323_);
lean_dec(v___x_4321_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_val_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
v___y_4272_ = v___y_4313_;
v___y_4273_ = v_args_4310_;
v___y_4274_ = v___y_4317_;
v___y_4275_ = v___y_4307_;
v___y_4276_ = v___y_4308_;
v___y_4277_ = v___y_4316_;
v___y_4278_ = v___y_4306_;
v___y_4279_ = v___y_4318_;
v___y_4280_ = v___y_4315_;
v___y_4281_ = v___y_4314_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4309_;
v___y_4285_ = v___x_4328_;
goto v___jp_4271_;
}
}
}
}
v___jp_4332_:
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = l_Lean_Syntax_getArg(v___y_4333_, v___y_4335_);
v___x_4348_ = l_Lean_Syntax_isNone(v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
lean_inc(v___x_4347_);
v___x_4349_ = l_Lean_Syntax_matchesNull(v___x_4347_, v___x_4331_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_dec(v___x_4347_);
lean_dec(v_o_4338_);
lean_dec(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec(v___y_4333_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4350_;
}
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4351_ = l_Lean_Syntax_getArg(v___x_4347_, v___x_3950_);
lean_dec(v___x_4347_);
v___x_4352_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
lean_inc_ref(v___x_3937_);
v___x_4353_ = l_Lean_Name_mkStr4(v___x_3937_, v___x_3938_, v___x_3939_, v___x_4352_);
lean_inc(v___x_4351_);
v___x_4354_ = l_Lean_Syntax_isOfKind(v___x_4351_, v___x_4353_);
lean_dec(v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
lean_dec(v___x_4351_);
lean_dec(v_o_4338_);
lean_dec(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec(v___y_4333_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; lean_object* v_args_4357_; lean_object* v___x_4358_; 
v___x_4356_ = l_Lean_Syntax_getArg(v___x_4351_, v___x_4331_);
lean_dec(v___x_4351_);
v_args_4357_ = l_Lean_Syntax_getArgs(v___x_4356_);
lean_dec(v___x_4356_);
v___x_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4358_, 0, v_args_4357_);
v___y_4305_ = v___y_4333_;
v___y_4306_ = v_o_4338_;
v___y_4307_ = v___y_4334_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v_args_4310_ = v___x_4358_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4340_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
goto v___jp_4304_;
}
}
}
else
{
lean_object* v___x_4359_; 
lean_dec(v___x_4347_);
v___x_4359_ = lean_box(0);
v___y_4305_ = v___y_4333_;
v___y_4306_ = v_o_4338_;
v___y_4307_ = v___y_4334_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v_args_4310_ = v___x_4359_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4340_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
goto v___jp_4304_;
}
}
v___jp_4360_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4370_ = lean_unsigned_to_nat(2u);
v___x_4371_ = l_Lean_Syntax_getArg(v_stx_3935_, v___x_4370_);
v___x_4372_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
lean_inc_ref(v___x_3937_);
v___x_4373_ = l_Lean_Name_mkStr4(v___x_3937_, v___x_3938_, v___x_3939_, v___x_4372_);
lean_inc(v___x_4371_);
v___x_4374_ = l_Lean_Syntax_isOfKind(v___x_4371_, v___x_4373_);
lean_dec(v___x_4373_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; 
lean_dec(v___x_4371_);
lean_dec(v_bang_4361_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4375_;
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4376_ = l_Lean_Syntax_getArg(v___x_4371_, v___x_3950_);
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
lean_inc_ref(v___x_3937_);
v___x_4378_ = l_Lean_Name_mkStr4(v___x_3937_, v___x_3938_, v___x_3939_, v___x_4377_);
lean_inc(v___x_4376_);
v___x_4379_ = l_Lean_Syntax_isOfKind(v___x_4376_, v___x_4378_);
lean_dec(v___x_4378_);
if (v___x_4379_ == 0)
{
lean_object* v___x_4380_; 
lean_dec(v___x_4376_);
lean_dec(v___x_4371_);
lean_dec(v_bang_4361_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4380_;
}
else
{
lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = l_Lean_Syntax_getArg(v___x_4371_, v___x_4331_);
v___x_4382_ = l_Lean_Syntax_isNone(v___x_4381_);
if (v___x_4382_ == 0)
{
uint8_t v___x_4383_; 
lean_inc(v___x_4381_);
v___x_4383_ = l_Lean_Syntax_matchesNull(v___x_4381_, v___x_4331_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_dec(v___x_4381_);
lean_dec(v___x_4376_);
lean_dec(v___x_4371_);
lean_dec(v_bang_4361_);
lean_dec(v_tk_3951_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
v___x_4384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4384_;
}
else
{
lean_object* v_o_4385_; lean_object* v___x_4386_; 
v_o_4385_ = l_Lean_Syntax_getArg(v___x_4381_, v___x_3950_);
lean_dec(v___x_4381_);
v___x_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4386_, 0, v_o_4385_);
v___y_4333_ = v___x_4371_;
v___y_4334_ = v___x_4379_;
v___y_4335_ = v___x_4370_;
v___y_4336_ = v___x_4376_;
v___y_4337_ = v_bang_4361_;
v_o_4338_ = v___x_4386_;
v___y_4339_ = v___y_4362_;
v___y_4340_ = v___y_4363_;
v___y_4341_ = v___y_4364_;
v___y_4342_ = v___y_4365_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
goto v___jp_4332_;
}
}
else
{
lean_object* v___x_4387_; 
lean_dec(v___x_4381_);
v___x_4387_ = lean_box(0);
v___y_4333_ = v___x_4371_;
v___y_4334_ = v___x_4379_;
v___y_4335_ = v___x_4370_;
v___y_4336_ = v___x_4376_;
v___y_4337_ = v_bang_4361_;
v_o_4338_ = v___x_4387_;
v___y_4339_ = v___y_4362_;
v___y_4340_ = v___y_4363_;
v___y_4341_ = v___y_4364_;
v___y_4342_ = v___y_4365_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
goto v___jp_4332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4395_, lean_object* v_stx_4396_, lean_object* v___x_4397_, lean_object* v___x_4398_, lean_object* v___x_4399_, lean_object* v___x_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
uint8_t v___x_10526__boxed_4410_; uint8_t v___x_10527__boxed_4411_; lean_object* v_res_4412_; 
v___x_10526__boxed_4410_ = lean_unbox(v___x_4395_);
v___x_10527__boxed_4411_ = lean_unbox(v___x_4397_);
v_res_4412_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10526__boxed_4410_, v_stx_4396_, v___x_10527__boxed_4411_, v___x_4398_, v___x_4399_, v___x_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v_stx_4396_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___y_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4419_);
v___x_4433_ = l_Lean_Syntax_isOfKind(v_stx_4419_, v___x_4432_);
v___x_4434_ = 1;
v___x_4435_ = lean_box(v___x_4433_);
v___x_4436_ = lean_box(v___x_4434_);
v___y_4437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4437_, 0, v___x_4435_);
lean_closure_set(v___y_4437_, 1, v_stx_4419_);
lean_closure_set(v___y_4437_, 2, v___x_4436_);
lean_closure_set(v___y_4437_, 3, v___x_4429_);
lean_closure_set(v___y_4437_, 4, v___x_4430_);
lean_closure_set(v___y_4437_, 5, v___x_4431_);
v___x_4438_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4438_, 0, v___y_4437_);
v___x_4439_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4438_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4458_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4462_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4458_, v___x_4459_, v___x_4460_, v___x_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4493_ = l_Lean_addBuiltinDeclarationRanges(v___x_4491_, v___x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4495_;
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
