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
uint8_t v___x_38778__boxed_208_; lean_object* v_res_209_; 
v___x_38778__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38778__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_38805__boxed_246_; lean_object* v_res_247_; 
v___x_38805__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_38805__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
uint8_t v___y_39004__boxed_379_; uint8_t v_suppressElabErrors_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v___y_39004__boxed_379_ = lean_unbox(v___y_376_);
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_377_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v___y_39004__boxed_379_, v_suppressElabErrors_boxed_380_, v_x_378_);
lean_dec(v_x_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; uint8_t v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_430_; lean_object* v___y_431_; uint8_t v___y_432_; uint8_t v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_466_; lean_object* v___y_467_; uint8_t v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; uint8_t v___y_472_; uint8_t v___x_477_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; uint8_t v___y_484_; uint8_t v___y_485_; uint8_t v___y_487_; uint8_t v___x_502_; 
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
lean_ctor_set(v___x_419_, 1, v___y_394_);
lean_inc_ref(v___y_395_);
lean_inc_ref(v___y_397_);
v___x_420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_420_, 0, v___y_397_);
lean_ctor_set(v___x_420_, 1, v___y_400_);
lean_ctor_set(v___x_420_, 2, v___y_396_);
lean_ctor_set(v___x_420_, 3, v___y_395_);
lean_ctor_set(v___x_420_, 4, v___x_419_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5, v___y_399_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5 + 1, v___y_398_);
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
lean_inc_ref_n(v___y_434_, 2);
v___x_444_ = l_Lean_FileMap_toPosition(v___y_434_, v___y_435_);
lean_dec(v___y_435_);
v___x_445_ = l_Lean_FileMap_toPosition(v___y_434_, v___y_437_);
lean_dec(v___y_437_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_442_);
lean_dec_ref(v___y_430_);
v___y_394_ = v_a_440_;
v___y_395_ = v___x_447_;
v___y_396_ = v___x_446_;
v___y_397_ = v___y_431_;
v___y_398_ = v___y_433_;
v___y_399_ = v___y_432_;
v___y_400_ = v___x_444_;
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
lean_dec_ref_known(v___x_446_, 1);
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
v___y_394_ = v_a_440_;
v___y_395_ = v___x_447_;
v___y_396_ = v___x_446_;
v___y_397_ = v___y_431_;
v___y_398_ = v___y_433_;
v___y_399_ = v___y_432_;
v___y_400_ = v___x_444_;
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
v___x_463_ = l_Lean_Syntax_getTailPos_x3f(v___y_456_, v___y_459_);
lean_dec(v___y_456_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_inc(v___y_462_);
v___y_430_ = v___y_455_;
v___y_431_ = v___y_457_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_458_;
v___y_434_ = v___y_460_;
v___y_435_ = v___y_462_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_462_;
goto v___jp_429_;
}
else
{
lean_object* v_val_464_; 
v_val_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___x_463_, 1);
v___y_430_ = v___y_455_;
v___y_431_ = v___y_457_;
v___y_432_ = v___y_459_;
v___y_433_ = v___y_458_;
v___y_434_ = v___y_460_;
v___y_435_ = v___y_462_;
v___y_436_ = v___y_461_;
v___y_437_ = v_val_464_;
goto v___jp_429_;
}
}
v___jp_465_:
{
lean_object* v_ref_473_; lean_object* v___x_474_; 
v_ref_473_ = l_Lean_replaceRef(v_ref_384_, v___y_469_);
v___x_474_ = l_Lean_Syntax_getPos_x3f(v_ref_473_, v___y_468_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___y_455_ = v___y_466_;
v___y_456_ = v_ref_473_;
v___y_457_ = v___y_467_;
v___y_458_ = v___y_472_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_470_;
v___y_461_ = v___y_471_;
v___y_462_ = v___x_475_;
goto v___jp_454_;
}
else
{
lean_object* v_val_476_; 
v_val_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_474_, 1);
v___y_455_ = v___y_466_;
v___y_456_ = v_ref_473_;
v___y_457_ = v___y_467_;
v___y_458_ = v___y_472_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_470_;
v___y_461_ = v___y_471_;
v___y_462_ = v_val_476_;
goto v___jp_454_;
}
}
v___jp_478_:
{
if (v___y_485_ == 0)
{
v___y_466_ = v___y_481_;
v___y_467_ = v___y_479_;
v___y_468_ = v___y_484_;
v___y_469_ = v___y_480_;
v___y_470_ = v___y_482_;
v___y_471_ = v___y_483_;
v___y_472_ = v_severity_386_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___y_481_;
v___y_467_ = v___y_479_;
v___y_468_ = v___y_484_;
v___y_469_ = v___y_480_;
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
v___y_479_ = v_fileName_488_;
v___y_480_ = v_ref_491_;
v___y_481_ = v___f_495_;
v___y_482_ = v_fileMap_489_;
v___y_483_ = v_suppressElabErrors_492_;
v___y_484_ = v___y_487_;
v___y_485_ = v___x_497_;
goto v___jp_478_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = l_Lean_warningAsError;
v___x_499_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_490_, v___x_498_);
v___y_479_ = v_fileName_488_;
v___y_480_ = v_ref_491_;
v___y_481_ = v___f_495_;
v___y_482_ = v_fileMap_489_;
v___y_483_ = v_suppressElabErrors_492_;
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
lean_dec_ref_known(v___x_642_, 1);
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
lean_dec_ref_known(v___x_758_, 14);
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
lean_dec_ref_known(v___x_1028_, 1);
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
lean_dec_ref_known(v_a_1050_, 2);
v_n_1056_ = lean_ctor_get(v_head_1053_, 0);
lean_inc(v_n_1056_);
lean_dec_ref_known(v_head_1053_, 2);
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
lean_dec_ref_known(v_a_1050_, 2);
v_a_1050_ = v_tail_1059_;
goto _start;
}
}
else
{
lean_object* v_tail_1061_; 
v_tail_1061_ = lean_ctor_get(v_a_1050_, 1);
lean_inc(v_tail_1061_);
lean_dec_ref_known(v_a_1050_, 2);
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
lean_dec_ref_known(v_stx_1070_, 4);
lean_dec(v_val_1081_);
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
lean_dec_ref_known(v_stx_1070_, 4);
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
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1161_, v_a_1163_, v_b_1147_, v___y_1154_);
lean_dec(v_a_1163_);
lean_dec(v___x_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; size_t v___x_1166_; size_t v___x_1167_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
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
lean_object* v___x_1229_; lean_object* v_tk_1230_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1302_; uint8_t v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1305_; lean_object* v___y_1306_; lean_object* v_stxForSuggestion_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1339_; uint8_t v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1366_; uint8_t v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1463_; uint8_t v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1501_; uint8_t v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1550_; uint8_t v___y_1551_; lean_object* v___y_1564_; uint8_t v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v_stxForExecution_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; uint8_t v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1670_; uint8_t v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; uint8_t v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; uint8_t v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v_argsArray_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1865_; lean_object* v___y_1866_; uint8_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; uint8_t v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; uint8_t v___y_2005_; lean_object* v___y_2006_; lean_object* v_args_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___x_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; uint8_t v___y_2033_; lean_object* v___y_2034_; lean_object* v_o_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_bang_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v_tk_1230_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_1229_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2087_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_2028_);
v___x_2088_ = l_Lean_Syntax_isNone(v___x_2087_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
lean_inc(v___x_2087_);
v___x_2089_ = l_Lean_Syntax_matchesNull(v___x_2087_, v___x_2028_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v___x_2087_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v_bang_2091_; lean_object* v___x_2092_; 
v_bang_2091_ = l_Lean_Syntax_getArg(v___x_2087_, v___x_1229_);
lean_dec(v___x_2087_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_bang_2091_);
v_bang_2059_ = v___x_2092_;
v___y_2060_ = v___y_1219_;
v___y_2061_ = v___y_1220_;
v___y_2062_ = v___y_1221_;
v___y_2063_ = v___y_1222_;
v___y_2064_ = v___y_1223_;
v___y_2065_ = v___y_1224_;
v___y_2066_ = v___y_1225_;
v___y_2067_ = v___y_1226_;
goto v___jp_2058_;
}
}
else
{
lean_object* v___x_2093_; 
lean_dec(v___x_2087_);
v___x_2093_ = lean_box(0);
v_bang_2059_ = v___x_2093_;
v___y_2060_ = v___y_1219_;
v___y_2061_ = v___y_1220_;
v___y_2062_ = v___y_1221_;
v___y_2063_ = v___y_1222_;
v___y_2064_ = v___y_1223_;
v___y_2065_ = v___y_1224_;
v___y_2066_ = v___y_1225_;
v___y_2067_ = v___y_1226_;
goto v___jp_2058_;
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
v___x_1247_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1234_, v___f_1246_, v___y_1241_, v___y_1240_, v___y_1243_, v___y_1239_, v___y_1235_, v___y_1242_, v___y_1238_, v___y_1236_);
lean_dec(v___y_1234_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v_usedTheorems_1249_; lean_object* v_diag_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1292_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v_usedTheorems_1249_ = lean_ctor_get(v_a_1248_, 0);
v_diag_1250_ = lean_ctor_get(v_a_1248_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1252_ = v_a_1248_;
v_isShared_1253_ = v_isSharedCheck_1292_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_diag_1250_);
lean_inc(v_usedTheorems_1249_);
lean_dec(v_a_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1292_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1237_, v_usedTheorems_1249_, v___y_1235_, v___y_1242_, v___y_1238_, v___y_1236_);
lean_dec_ref(v_usedTheorems_1249_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_ref_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_ref_1256_ = lean_ctor_get(v___y_1238_, 5);
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
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1255_);
v___x_1259_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
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
v___x_1265_ = l_Lean_MessageData_nil;
v___x_1266_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1230_, v___x_1261_, v___x_1262_, v___x_1263_, v___x_1260_, v___x_1264_, v___x_1265_, v___y_1238_, v___y_1236_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1274_);
v___x_1268_ = v___x_1266_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v_diag_1250_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_diag_1250_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v_diag_1250_);
v_a_1275_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1266_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1266_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1252_);
lean_dec_ref(v_diag_1250_);
lean_dec(v_tk_1230_);
v_a_1284_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1254_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1254_);
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
lean_dec(v___y_1237_);
lean_dec(v_tk_1230_);
v_a_1293_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1247_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1247_);
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
v___jp_1301_:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = 0;
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1318_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1306_, v___x_1316_, v___y_1303_, v___x_1316_, v___x_1317_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1306_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
if (lean_obj_tag(v___y_1304_) == 0)
{
lean_object* v_ctx_1320_; lean_object* v_simprocs_1321_; lean_object* v_dischargeWrapper_1322_; 
v_ctx_1320_ = lean_ctor_get(v_a_1319_, 0);
lean_inc_ref(v_ctx_1320_);
v_simprocs_1321_ = lean_ctor_get(v_a_1319_, 1);
lean_inc_ref(v_simprocs_1321_);
v_dischargeWrapper_1322_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_dischargeWrapper_1322_);
lean_dec(v_a_1319_);
v___y_1232_ = v___y_1302_;
v___y_1233_ = v_simprocs_1321_;
v___y_1234_ = v_dischargeWrapper_1322_;
v___y_1235_ = v___y_1312_;
v___y_1236_ = v___y_1315_;
v___y_1237_ = v_stxForSuggestion_1307_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1311_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1308_;
v___y_1242_ = v___y_1313_;
v___y_1243_ = v___y_1310_;
v___y_1244_ = v_ctx_1320_;
goto v___jp_1231_;
}
else
{
lean_dec_ref_known(v___y_1304_, 1);
if (v___y_1305_ == 0)
{
lean_object* v_ctx_1323_; lean_object* v_simprocs_1324_; lean_object* v_dischargeWrapper_1325_; 
v_ctx_1323_ = lean_ctor_get(v_a_1319_, 0);
lean_inc_ref(v_ctx_1323_);
v_simprocs_1324_ = lean_ctor_get(v_a_1319_, 1);
lean_inc_ref(v_simprocs_1324_);
v_dischargeWrapper_1325_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_dischargeWrapper_1325_);
lean_dec(v_a_1319_);
v___y_1232_ = v___y_1302_;
v___y_1233_ = v_simprocs_1324_;
v___y_1234_ = v_dischargeWrapper_1325_;
v___y_1235_ = v___y_1312_;
v___y_1236_ = v___y_1315_;
v___y_1237_ = v_stxForSuggestion_1307_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1311_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1308_;
v___y_1242_ = v___y_1313_;
v___y_1243_ = v___y_1310_;
v___y_1244_ = v_ctx_1323_;
goto v___jp_1231_;
}
else
{
lean_object* v_ctx_1326_; lean_object* v_simprocs_1327_; lean_object* v_dischargeWrapper_1328_; lean_object* v___x_1329_; 
v_ctx_1326_ = lean_ctor_get(v_a_1319_, 0);
lean_inc_ref(v_ctx_1326_);
v_simprocs_1327_ = lean_ctor_get(v_a_1319_, 1);
lean_inc_ref(v_simprocs_1327_);
v_dischargeWrapper_1328_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_dischargeWrapper_1328_);
lean_dec(v_a_1319_);
v___x_1329_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1326_);
v___y_1232_ = v___y_1302_;
v___y_1233_ = v_simprocs_1327_;
v___y_1234_ = v_dischargeWrapper_1328_;
v___y_1235_ = v___y_1312_;
v___y_1236_ = v___y_1315_;
v___y_1237_ = v_stxForSuggestion_1307_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1311_;
v___y_1240_ = v___y_1309_;
v___y_1241_ = v___y_1308_;
v___y_1242_ = v___y_1313_;
v___y_1243_ = v___y_1310_;
v___y_1244_ = v___x_1329_;
goto v___jp_1231_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_stxForSuggestion_1307_);
lean_dec(v___y_1304_);
lean_dec(v___y_1302_);
lean_dec(v_tk_1230_);
v_a_1330_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1318_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1318_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v___y_1356_);
v___x_1362_ = l_Array_append___redArg(v___y_1356_, v___y_1361_);
lean_dec_ref(v___y_1361_);
lean_inc(v___y_1349_);
lean_inc(v___y_1341_);
v___x_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1341_);
lean_ctor_set(v___x_1363_, 1, v___y_1349_);
lean_ctor_set(v___x_1363_, 2, v___x_1362_);
v___x_1364_ = l_Lean_Syntax_node6(v___y_1341_, v___y_1342_, v___y_1352_, v___y_1345_, v___y_1351_, v___y_1344_, v___y_1358_, v___x_1363_);
v___y_1302_ = v___y_1339_;
v___y_1303_ = v___y_1340_;
v___y_1304_ = v___y_1354_;
v___y_1305_ = v___y_1357_;
v___y_1306_ = v___y_1347_;
v_stxForSuggestion_1307_ = v___x_1364_;
v___y_1308_ = v___y_1353_;
v___y_1309_ = v___y_1359_;
v___y_1310_ = v___y_1348_;
v___y_1311_ = v___y_1350_;
v___y_1312_ = v___y_1346_;
v___y_1313_ = v___y_1343_;
v___y_1314_ = v___y_1355_;
v___y_1315_ = v___y_1360_;
goto v___jp_1301_;
}
v___jp_1365_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc_ref_n(v___y_1384_, 2);
v___x_1389_ = l_Array_append___redArg(v___y_1384_, v___y_1388_);
lean_dec_ref(v___y_1388_);
lean_inc_n(v___y_1377_, 3);
lean_inc_n(v___y_1368_, 5);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___y_1368_);
lean_ctor_set(v___x_1390_, 1, v___y_1377_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1368_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1394_ = l_Lean_Syntax_SepArray_ofElems(v___x_1393_, v___y_1369_);
lean_dec_ref(v___y_1369_);
v___x_1395_ = l_Array_append___redArg(v___y_1384_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1368_);
lean_ctor_set(v___x_1396_, 1, v___y_1377_);
lean_ctor_set(v___x_1396_, 2, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___y_1368_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_Syntax_node3(v___y_1368_, v___y_1377_, v___x_1392_, v___x_1396_, v___x_1398_);
if (lean_obj_tag(v___y_1374_) == 1)
{
lean_object* v_val_1400_; lean_object* v___x_1401_; 
v_val_1400_ = lean_ctor_get(v___y_1374_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___y_1374_, 1);
v___x_1401_ = l_Array_mkArray1___redArg(v_val_1400_);
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1370_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v___x_1390_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
v___y_1353_ = v___y_1381_;
v___y_1354_ = v___y_1383_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1384_;
v___y_1357_ = v___y_1386_;
v___y_1358_ = v___x_1399_;
v___y_1359_ = v___y_1385_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___x_1401_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1402_; 
lean_dec(v___y_1374_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1370_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v___x_1390_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
v___y_1353_ = v___y_1381_;
v___y_1354_ = v___y_1383_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1384_;
v___y_1357_ = v___y_1386_;
v___y_1358_ = v___x_1399_;
v___y_1359_ = v___y_1385_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___x_1402_;
goto v___jp_1338_;
}
}
v___jp_1403_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_inc_ref(v___y_1422_);
v___x_1427_ = l_Array_append___redArg(v___y_1422_, v___y_1426_);
lean_dec_ref(v___y_1426_);
lean_inc(v___y_1417_);
lean_inc(v___y_1406_);
v___x_1428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1406_);
lean_ctor_set(v___x_1428_, 1, v___y_1417_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
if (lean_obj_tag(v___y_1408_) == 1)
{
lean_object* v_val_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_val_1429_ = lean_ctor_get(v___y_1408_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___y_1408_, 1);
v___x_1430_ = l_Lean_SourceInfo_fromRef(v_val_1429_, v___x_1214_);
lean_dec(v_val_1429_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Array_mkArray1___redArg(v___x_1432_);
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1415_;
v___y_1377_ = v___y_1417_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___x_1428_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1420_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1423_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___x_1433_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1434_; 
lean_dec(v___y_1408_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1415_;
v___y_1377_ = v___y_1417_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___x_1428_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1420_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___y_1423_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___x_1434_;
goto v___jp_1365_;
}
}
v___jp_1435_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v___y_1438_);
v___x_1459_ = l_Array_append___redArg(v___y_1438_, v___y_1458_);
lean_dec_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc(v___y_1455_);
v___x_1460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1455_);
lean_ctor_set(v___x_1460_, 1, v___y_1457_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node6(v___y_1455_, v___y_1441_, v___y_1440_, v___y_1442_, v___y_1450_, v___y_1451_, v___y_1453_, v___x_1460_);
v___y_1302_ = v___y_1436_;
v___y_1303_ = v___y_1437_;
v___y_1304_ = v___y_1448_;
v___y_1305_ = v___y_1452_;
v___y_1306_ = v___y_1444_;
v_stxForSuggestion_1307_ = v___x_1461_;
v___y_1308_ = v___y_1447_;
v___y_1309_ = v___y_1454_;
v___y_1310_ = v___y_1445_;
v___y_1311_ = v___y_1446_;
v___y_1312_ = v___y_1443_;
v___y_1313_ = v___y_1439_;
v___y_1314_ = v___y_1449_;
v___y_1315_ = v___y_1456_;
goto v___jp_1301_;
}
v___jp_1462_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_inc_ref_n(v___y_1465_, 2);
v___x_1486_ = l_Array_append___redArg(v___y_1465_, v___y_1485_);
lean_dec_ref(v___y_1485_);
lean_inc_n(v___y_1484_, 3);
lean_inc_n(v___y_1482_, 5);
v___x_1487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1482_);
lean_ctor_set(v___x_1487_, 1, v___y_1484_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1482_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1491_ = l_Lean_Syntax_SepArray_ofElems(v___x_1490_, v___y_1466_);
lean_dec_ref(v___y_1466_);
v___x_1492_ = l_Array_append___redArg(v___y_1465_, v___x_1491_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1493_, 0, v___y_1482_);
lean_ctor_set(v___x_1493_, 1, v___y_1484_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1482_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Lean_Syntax_node3(v___y_1482_, v___y_1484_, v___x_1489_, v___x_1493_, v___x_1495_);
if (lean_obj_tag(v___y_1472_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1498_; 
v_val_1497_ = lean_ctor_get(v___y_1472_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___y_1472_, 1);
v___x_1498_ = l_Array_mkArray1___redArg(v_val_1497_);
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1468_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___y_1470_;
v___y_1443_ = v___y_1471_;
v___y_1444_ = v___y_1473_;
v___y_1445_ = v___y_1474_;
v___y_1446_ = v___y_1475_;
v___y_1447_ = v___y_1476_;
v___y_1448_ = v___y_1479_;
v___y_1449_ = v___y_1478_;
v___y_1450_ = v___y_1477_;
v___y_1451_ = v___x_1487_;
v___y_1452_ = v___y_1481_;
v___y_1453_ = v___x_1496_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___x_1498_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1499_; 
lean_dec(v___y_1472_);
v___x_1499_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1468_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___y_1470_;
v___y_1443_ = v___y_1471_;
v___y_1444_ = v___y_1473_;
v___y_1445_ = v___y_1474_;
v___y_1446_ = v___y_1475_;
v___y_1447_ = v___y_1476_;
v___y_1448_ = v___y_1479_;
v___y_1449_ = v___y_1478_;
v___y_1450_ = v___y_1477_;
v___y_1451_ = v___x_1487_;
v___y_1452_ = v___y_1481_;
v___y_1453_ = v___x_1496_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___x_1499_;
goto v___jp_1435_;
}
}
v___jp_1500_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_inc_ref(v___y_1503_);
v___x_1524_ = l_Array_append___redArg(v___y_1503_, v___y_1523_);
lean_dec_ref(v___y_1523_);
lean_inc(v___y_1522_);
lean_inc(v___y_1520_);
v___x_1525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1525_, 0, v___y_1520_);
lean_ctor_set(v___x_1525_, 1, v___y_1522_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
if (lean_obj_tag(v___y_1505_) == 1)
{
lean_object* v_val_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_val_1526_ = lean_ctor_get(v___y_1505_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___y_1505_, 1);
v___x_1527_ = l_Lean_SourceInfo_fromRef(v_val_1526_, v___x_1214_);
lean_dec(v_val_1526_);
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l_Array_mkArray1___redArg(v___x_1529_);
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1506_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1510_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1512_;
v___y_1474_ = v___y_1513_;
v___y_1475_ = v___y_1514_;
v___y_1476_ = v___y_1515_;
v___y_1477_ = v___x_1525_;
v___y_1478_ = v___y_1517_;
v___y_1479_ = v___y_1516_;
v___y_1480_ = v___y_1519_;
v___y_1481_ = v___y_1518_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___x_1530_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1531_; 
lean_dec(v___y_1505_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1506_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1510_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1512_;
v___y_1474_ = v___y_1513_;
v___y_1475_ = v___y_1514_;
v___y_1476_ = v___y_1515_;
v___y_1477_ = v___x_1525_;
v___y_1478_ = v___y_1517_;
v___y_1479_ = v___y_1516_;
v___y_1480_ = v___y_1519_;
v___y_1481_ = v___y_1518_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___x_1531_;
goto v___jp_1462_;
}
}
v___jp_1532_:
{
lean_object* v_ref_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_ref_1552_ = lean_ctor_get(v___y_1547_, 5);
v___x_1553_ = l_Lean_SourceInfo_fromRef(v_ref_1552_, v___y_1551_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1555_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1554_);
v___x_1556_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1554_);
v___x_1558_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1559_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1539_) == 1)
{
lean_object* v_val_1560_; lean_object* v___x_1561_; 
v_val_1560_ = lean_ctor_get(v___y_1539_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v___y_1539_, 1);
v___x_1561_ = l_Array_mkArray1___redArg(v_val_1560_);
v___y_1501_ = v___y_1533_;
v___y_1502_ = v___y_1534_;
v___y_1503_ = v___x_1559_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1536_;
v___y_1506_ = v___y_1537_;
v___y_1507_ = v___x_1557_;
v___y_1508_ = v___x_1555_;
v___y_1509_ = v___y_1538_;
v___y_1510_ = v___y_1540_;
v___y_1511_ = v___y_1541_;
v___y_1512_ = v___y_1542_;
v___y_1513_ = v___y_1543_;
v___y_1514_ = v___y_1544_;
v___y_1515_ = v___y_1545_;
v___y_1516_ = v___y_1546_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___y_1549_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___x_1553_;
v___y_1521_ = v___y_1550_;
v___y_1522_ = v___x_1558_;
v___y_1523_ = v___x_1561_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1562_; 
lean_dec(v___y_1539_);
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1501_ = v___y_1533_;
v___y_1502_ = v___y_1534_;
v___y_1503_ = v___x_1559_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1536_;
v___y_1506_ = v___y_1537_;
v___y_1507_ = v___x_1557_;
v___y_1508_ = v___x_1555_;
v___y_1509_ = v___y_1538_;
v___y_1510_ = v___y_1540_;
v___y_1511_ = v___y_1541_;
v___y_1512_ = v___y_1542_;
v___y_1513_ = v___y_1543_;
v___y_1514_ = v___y_1544_;
v___y_1515_ = v___y_1545_;
v___y_1516_ = v___y_1546_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___y_1549_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___x_1553_;
v___y_1521_ = v___y_1550_;
v___y_1522_ = v___x_1558_;
v___y_1523_ = v___x_1562_;
goto v___jp_1500_;
}
}
v___jp_1563_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___y_1568_) == 0)
{
lean_object* v_a_1583_; uint8_t v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = 0;
v___y_1533_ = v___y_1564_;
v___y_1534_ = v___y_1565_;
v___y_1535_ = v___y_1566_;
v___y_1536_ = v___y_1567_;
v___y_1537_ = v___y_1579_;
v___y_1538_ = v_a_1583_;
v___y_1539_ = v___y_1569_;
v___y_1540_ = v___y_1578_;
v___y_1541_ = v___y_1571_;
v___y_1542_ = v_stxForExecution_1573_;
v___y_1543_ = v___y_1576_;
v___y_1544_ = v___y_1577_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1575_;
v___y_1549_ = v___y_1570_;
v___y_1550_ = v___y_1581_;
v___y_1551_ = v___x_1584_;
goto v___jp_1532_;
}
else
{
if (v___y_1570_ == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1582_);
v___y_1533_ = v___y_1564_;
v___y_1534_ = v___y_1565_;
v___y_1535_ = v___y_1566_;
v___y_1536_ = v___y_1567_;
v___y_1537_ = v___y_1579_;
v___y_1538_ = v_a_1585_;
v___y_1539_ = v___y_1569_;
v___y_1540_ = v___y_1578_;
v___y_1541_ = v___y_1571_;
v___y_1542_ = v_stxForExecution_1573_;
v___y_1543_ = v___y_1576_;
v___y_1544_ = v___y_1577_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1575_;
v___y_1549_ = v___y_1570_;
v___y_1550_ = v___y_1581_;
v___y_1551_ = v___y_1570_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1586_; lean_object* v_ref_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1586_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1582_);
v_ref_1587_ = lean_ctor_get(v___y_1580_, 5);
v___x_1588_ = 0;
v___x_1589_ = l_Lean_SourceInfo_fromRef(v_ref_1587_, v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1591_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1590_);
v___x_1592_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1593_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1596_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1569_) == 1)
{
lean_object* v_val_1597_; lean_object* v___x_1598_; 
v_val_1597_ = lean_ctor_get(v___y_1569_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v___y_1569_, 1);
v___x_1598_ = l_Array_mkArray1___redArg(v_val_1597_);
v___y_1404_ = v___y_1564_;
v___y_1405_ = v___y_1565_;
v___y_1406_ = v___x_1589_;
v___y_1407_ = v___y_1566_;
v___y_1408_ = v___y_1567_;
v___y_1409_ = v___x_1591_;
v___y_1410_ = v___y_1579_;
v___y_1411_ = v_a_1586_;
v___y_1412_ = v___y_1578_;
v___y_1413_ = v___y_1571_;
v___y_1414_ = v_stxForExecution_1573_;
v___y_1415_ = v___y_1576_;
v___y_1416_ = v___y_1577_;
v___y_1417_ = v___x_1595_;
v___y_1418_ = v___x_1594_;
v___y_1419_ = v___y_1574_;
v___y_1420_ = v___y_1568_;
v___y_1421_ = v___y_1580_;
v___y_1422_ = v___x_1596_;
v___y_1423_ = v___y_1570_;
v___y_1424_ = v___y_1575_;
v___y_1425_ = v___y_1581_;
v___y_1426_ = v___x_1598_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1599_; 
lean_dec(v___y_1569_);
v___x_1599_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1404_ = v___y_1564_;
v___y_1405_ = v___y_1565_;
v___y_1406_ = v___x_1589_;
v___y_1407_ = v___y_1566_;
v___y_1408_ = v___y_1567_;
v___y_1409_ = v___x_1591_;
v___y_1410_ = v___y_1579_;
v___y_1411_ = v_a_1586_;
v___y_1412_ = v___y_1578_;
v___y_1413_ = v___y_1571_;
v___y_1414_ = v_stxForExecution_1573_;
v___y_1415_ = v___y_1576_;
v___y_1416_ = v___y_1577_;
v___y_1417_ = v___x_1595_;
v___y_1418_ = v___x_1594_;
v___y_1419_ = v___y_1574_;
v___y_1420_ = v___y_1568_;
v___y_1421_ = v___y_1580_;
v___y_1422_ = v___x_1596_;
v___y_1423_ = v___y_1570_;
v___y_1424_ = v___y_1575_;
v___y_1425_ = v___y_1581_;
v___y_1426_ = v___x_1599_;
goto v___jp_1403_;
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_inc_ref(v___y_1609_);
v___x_1627_ = l_Array_append___redArg(v___y_1609_, v___y_1626_);
lean_dec_ref(v___y_1626_);
lean_inc(v___y_1612_);
lean_inc(v___y_1602_);
v___x_1628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1602_);
lean_ctor_set(v___x_1628_, 1, v___y_1612_);
lean_ctor_set(v___x_1628_, 2, v___x_1627_);
lean_inc(v___y_1621_);
v___x_1629_ = l_Lean_Syntax_node6(v___y_1602_, v___y_1624_, v___y_1605_, v___y_1621_, v___y_1611_, v___y_1622_, v___y_1615_, v___x_1628_);
v___y_1564_ = v___y_1601_;
v___y_1565_ = v___y_1618_;
v___y_1566_ = v___y_1603_;
v___y_1567_ = v___y_1604_;
v___y_1568_ = v___y_1623_;
v___y_1569_ = v___y_1606_;
v___y_1570_ = v___y_1616_;
v___y_1571_ = v___y_1607_;
v___y_1572_ = v___y_1621_;
v_stxForExecution_1573_ = v___x_1629_;
v___y_1574_ = v___y_1625_;
v___y_1575_ = v___y_1613_;
v___y_1576_ = v___y_1610_;
v___y_1577_ = v___y_1608_;
v___y_1578_ = v___y_1619_;
v___y_1579_ = v___y_1617_;
v___y_1580_ = v___y_1614_;
v___y_1581_ = v___y_1620_;
goto v___jp_1563_;
}
v___jp_1630_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_inc_ref_n(v___y_1641_, 2);
v___x_1655_ = l_Array_append___redArg(v___y_1641_, v___y_1654_);
lean_dec_ref(v___y_1654_);
lean_inc_n(v___y_1644_, 3);
lean_inc_n(v___y_1634_, 5);
v___x_1656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1634_);
lean_ctor_set(v___x_1656_, 1, v___y_1644_);
lean_ctor_set(v___x_1656_, 2, v___x_1655_);
v___x_1657_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___y_1634_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1660_ = l_Lean_Syntax_SepArray_ofElems(v___x_1659_, v___y_1635_);
v___x_1661_ = l_Array_append___redArg(v___y_1641_, v___x_1660_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1634_);
lean_ctor_set(v___x_1662_, 1, v___y_1644_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
v___x_1663_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1634_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_Syntax_node3(v___y_1634_, v___y_1644_, v___x_1658_, v___x_1662_, v___x_1664_);
if (lean_obj_tag(v___y_1640_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
v_val_1666_ = lean_ctor_get(v___y_1640_, 0);
lean_inc(v_val_1666_);
v___x_1667_ = l_Array_mkArray1___redArg(v_val_1666_);
v___y_1601_ = v___y_1631_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___y_1637_;
v___y_1606_ = v___y_1638_;
v___y_1607_ = v___y_1640_;
v___y_1608_ = v___y_1642_;
v___y_1609_ = v___y_1641_;
v___y_1610_ = v___y_1645_;
v___y_1611_ = v___y_1646_;
v___y_1612_ = v___y_1644_;
v___y_1613_ = v___y_1647_;
v___y_1614_ = v___y_1648_;
v___y_1615_ = v___x_1665_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___y_1653_;
v___y_1618_ = v___y_1632_;
v___y_1619_ = v___y_1633_;
v___y_1620_ = v___y_1639_;
v___y_1621_ = v___y_1643_;
v___y_1622_ = v___x_1656_;
v___y_1623_ = v___y_1649_;
v___y_1624_ = v___y_1651_;
v___y_1625_ = v___y_1652_;
v___y_1626_ = v___x_1667_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1601_ = v___y_1631_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___y_1637_;
v___y_1606_ = v___y_1638_;
v___y_1607_ = v___y_1640_;
v___y_1608_ = v___y_1642_;
v___y_1609_ = v___y_1641_;
v___y_1610_ = v___y_1645_;
v___y_1611_ = v___y_1646_;
v___y_1612_ = v___y_1644_;
v___y_1613_ = v___y_1647_;
v___y_1614_ = v___y_1648_;
v___y_1615_ = v___x_1665_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___y_1653_;
v___y_1618_ = v___y_1632_;
v___y_1619_ = v___y_1633_;
v___y_1620_ = v___y_1639_;
v___y_1621_ = v___y_1643_;
v___y_1622_ = v___x_1656_;
v___y_1623_ = v___y_1649_;
v___y_1624_ = v___y_1651_;
v___y_1625_ = v___y_1652_;
v___y_1626_ = v___x_1668_;
goto v___jp_1600_;
}
}
v___jp_1669_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_inc_ref(v___y_1680_);
v___x_1693_ = l_Array_append___redArg(v___y_1680_, v___y_1692_);
lean_dec_ref(v___y_1692_);
lean_inc(v___y_1684_);
lean_inc(v___y_1673_);
v___x_1694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1694_, 0, v___y_1673_);
lean_ctor_set(v___x_1694_, 1, v___y_1684_);
lean_ctor_set(v___x_1694_, 2, v___x_1693_);
if (lean_obj_tag(v___y_1675_) == 1)
{
lean_object* v_val_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_val_1695_ = lean_ctor_get(v___y_1675_, 0);
v___x_1696_ = l_Lean_SourceInfo_fromRef(v_val_1695_, v___x_1214_);
v___x_1697_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Array_mkArray1___redArg(v___x_1698_);
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1683_;
v___y_1644_ = v___y_1684_;
v___y_1645_ = v___y_1682_;
v___y_1646_ = v___x_1694_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1688_;
v___y_1651_ = v___y_1689_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___y_1690_;
v___y_1654_ = v___x_1699_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1683_;
v___y_1644_ = v___y_1684_;
v___y_1645_ = v___y_1682_;
v___y_1646_ = v___x_1694_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___y_1687_;
v___y_1650_ = v___y_1688_;
v___y_1651_ = v___y_1689_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___y_1690_;
v___y_1654_ = v___x_1700_;
goto v___jp_1630_;
}
}
v___jp_1701_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_inc_ref(v___y_1716_);
v___x_1728_ = l_Array_append___redArg(v___y_1716_, v___y_1727_);
lean_dec_ref(v___y_1727_);
lean_inc(v___y_1724_);
lean_inc(v___y_1715_);
v___x_1729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1729_, 0, v___y_1715_);
lean_ctor_set(v___x_1729_, 1, v___y_1724_);
lean_ctor_set(v___x_1729_, 2, v___x_1728_);
lean_inc(v___y_1723_);
v___x_1730_ = l_Lean_Syntax_node6(v___y_1715_, v___y_1709_, v___y_1708_, v___y_1723_, v___y_1721_, v___y_1722_, v___y_1712_, v___x_1729_);
v___y_1564_ = v___y_1702_;
v___y_1565_ = v___y_1718_;
v___y_1566_ = v___y_1703_;
v___y_1567_ = v___y_1704_;
v___y_1568_ = v___y_1725_;
v___y_1569_ = v___y_1705_;
v___y_1570_ = v___y_1714_;
v___y_1571_ = v___y_1706_;
v___y_1572_ = v___y_1723_;
v_stxForExecution_1573_ = v___x_1730_;
v___y_1574_ = v___y_1726_;
v___y_1575_ = v___y_1711_;
v___y_1576_ = v___y_1710_;
v___y_1577_ = v___y_1707_;
v___y_1578_ = v___y_1719_;
v___y_1579_ = v___y_1717_;
v___y_1580_ = v___y_1713_;
v___y_1581_ = v___y_1720_;
goto v___jp_1563_;
}
v___jp_1731_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_inc_ref_n(v___y_1751_, 2);
v___x_1756_ = l_Array_append___redArg(v___y_1751_, v___y_1755_);
lean_dec_ref(v___y_1755_);
lean_inc_n(v___y_1747_, 3);
lean_inc_n(v___y_1752_, 5);
v___x_1757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1752_);
lean_ctor_set(v___x_1757_, 1, v___y_1747_);
lean_ctor_set(v___x_1757_, 2, v___x_1756_);
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1752_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1761_ = l_Lean_Syntax_SepArray_ofElems(v___x_1760_, v___y_1735_);
v___x_1762_ = l_Array_append___redArg(v___y_1751_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1763_, 0, v___y_1752_);
lean_ctor_set(v___x_1763_, 1, v___y_1747_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1752_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_Syntax_node3(v___y_1752_, v___y_1747_, v___x_1759_, v___x_1763_, v___x_1765_);
if (lean_obj_tag(v___y_1739_) == 1)
{
lean_object* v_val_1767_; lean_object* v___x_1768_; 
v_val_1767_ = lean_ctor_get(v___y_1739_, 0);
lean_inc(v_val_1767_);
v___x_1768_ = l_Array_mkArray1___redArg(v_val_1767_);
v___y_1702_ = v___y_1732_;
v___y_1703_ = v___y_1735_;
v___y_1704_ = v___y_1736_;
v___y_1705_ = v___y_1737_;
v___y_1706_ = v___y_1739_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___y_1742_;
v___y_1709_ = v___y_1743_;
v___y_1710_ = v___y_1745_;
v___y_1711_ = v___y_1746_;
v___y_1712_ = v___x_1766_;
v___y_1713_ = v___y_1748_;
v___y_1714_ = v___y_1750_;
v___y_1715_ = v___y_1752_;
v___y_1716_ = v___y_1751_;
v___y_1717_ = v___y_1754_;
v___y_1718_ = v___y_1733_;
v___y_1719_ = v___y_1734_;
v___y_1720_ = v___y_1738_;
v___y_1721_ = v___y_1740_;
v___y_1722_ = v___x_1757_;
v___y_1723_ = v___y_1744_;
v___y_1724_ = v___y_1747_;
v___y_1725_ = v___y_1749_;
v___y_1726_ = v___y_1753_;
v___y_1727_ = v___x_1768_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1702_ = v___y_1732_;
v___y_1703_ = v___y_1735_;
v___y_1704_ = v___y_1736_;
v___y_1705_ = v___y_1737_;
v___y_1706_ = v___y_1739_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___y_1742_;
v___y_1709_ = v___y_1743_;
v___y_1710_ = v___y_1745_;
v___y_1711_ = v___y_1746_;
v___y_1712_ = v___x_1766_;
v___y_1713_ = v___y_1748_;
v___y_1714_ = v___y_1750_;
v___y_1715_ = v___y_1752_;
v___y_1716_ = v___y_1751_;
v___y_1717_ = v___y_1754_;
v___y_1718_ = v___y_1733_;
v___y_1719_ = v___y_1734_;
v___y_1720_ = v___y_1738_;
v___y_1721_ = v___y_1740_;
v___y_1722_ = v___x_1757_;
v___y_1723_ = v___y_1744_;
v___y_1724_ = v___y_1747_;
v___y_1725_ = v___y_1749_;
v___y_1726_ = v___y_1753_;
v___y_1727_ = v___x_1769_;
goto v___jp_1701_;
}
}
v___jp_1770_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_inc_ref(v___y_1789_);
v___x_1794_ = l_Array_append___redArg(v___y_1789_, v___y_1793_);
lean_dec_ref(v___y_1793_);
lean_inc(v___y_1785_);
lean_inc(v___y_1790_);
v___x_1795_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1795_, 0, v___y_1790_);
lean_ctor_set(v___x_1795_, 1, v___y_1785_);
lean_ctor_set(v___x_1795_, 2, v___x_1794_);
if (lean_obj_tag(v___y_1775_) == 1)
{
lean_object* v_val_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_val_1796_ = lean_ctor_get(v___y_1775_, 0);
v___x_1797_ = l_Lean_SourceInfo_fromRef(v_val_1796_, v___x_1214_);
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Array_mkArray1___redArg(v___x_1799_);
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1776_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___x_1795_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1779_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1782_;
v___y_1746_ = v___y_1784_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v___y_1786_;
v___y_1749_ = v___y_1787_;
v___y_1750_ = v___y_1788_;
v___y_1751_ = v___y_1789_;
v___y_1752_ = v___y_1790_;
v___y_1753_ = v___y_1792_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___x_1800_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1776_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___x_1795_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1779_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1782_;
v___y_1746_ = v___y_1784_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v___y_1786_;
v___y_1749_ = v___y_1787_;
v___y_1750_ = v___y_1788_;
v___y_1751_ = v___y_1789_;
v___y_1752_ = v___y_1790_;
v___y_1753_ = v___y_1792_;
v___y_1754_ = v___y_1791_;
v___y_1755_ = v___x_1801_;
goto v___jp_1731_;
}
}
v___jp_1802_:
{
lean_object* v_ref_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_ref_1821_ = lean_ctor_get(v___y_1815_, 5);
v___x_1822_ = l_Lean_SourceInfo_fromRef(v_ref_1821_, v___y_1820_);
v___x_1823_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_1824_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1823_);
v___x_1825_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1823_);
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1828_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1808_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; 
v_val_1829_ = lean_ctor_get(v___y_1808_, 0);
lean_inc(v_val_1829_);
v___x_1830_ = l_Array_mkArray1___redArg(v_val_1829_);
v___y_1771_ = v___y_1803_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1805_;
v___y_1774_ = v___y_1806_;
v___y_1775_ = v___y_1807_;
v___y_1776_ = v___y_1808_;
v___y_1777_ = v___y_1809_;
v___y_1778_ = v___y_1810_;
v___y_1779_ = v___x_1824_;
v___y_1780_ = v___y_1811_;
v___y_1781_ = v___x_1826_;
v___y_1782_ = v___y_1812_;
v___y_1783_ = v___y_1813_;
v___y_1784_ = v___y_1814_;
v___y_1785_ = v___x_1827_;
v___y_1786_ = v___y_1815_;
v___y_1787_ = v___y_1816_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___x_1828_;
v___y_1790_ = v___x_1822_;
v___y_1791_ = v___y_1819_;
v___y_1792_ = v___y_1818_;
v___y_1793_ = v___x_1830_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1771_ = v___y_1803_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1805_;
v___y_1774_ = v___y_1806_;
v___y_1775_ = v___y_1807_;
v___y_1776_ = v___y_1808_;
v___y_1777_ = v___y_1809_;
v___y_1778_ = v___y_1810_;
v___y_1779_ = v___x_1824_;
v___y_1780_ = v___y_1811_;
v___y_1781_ = v___x_1826_;
v___y_1782_ = v___y_1812_;
v___y_1783_ = v___y_1813_;
v___y_1784_ = v___y_1814_;
v___y_1785_ = v___x_1827_;
v___y_1786_ = v___y_1815_;
v___y_1787_ = v___y_1816_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___x_1828_;
v___y_1790_ = v___x_1822_;
v___y_1791_ = v___y_1819_;
v___y_1792_ = v___y_1818_;
v___y_1793_ = v___x_1831_;
goto v___jp_1770_;
}
}
v___jp_1832_:
{
if (lean_obj_tag(v___y_1836_) == 0)
{
uint8_t v___x_1850_; 
v___x_1850_ = 0;
v___y_1803_ = v___y_1833_;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1846_;
v___y_1806_ = v_argsArray_1841_;
v___y_1807_ = v___y_1835_;
v___y_1808_ = v___y_1838_;
v___y_1809_ = v___y_1849_;
v___y_1810_ = v___y_1839_;
v___y_1811_ = v___y_1845_;
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___y_1840_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___y_1848_;
v___y_1816_ = v___y_1836_;
v___y_1817_ = v___y_1837_;
v___y_1818_ = v___y_1842_;
v___y_1819_ = v___y_1847_;
v___y_1820_ = v___x_1850_;
goto v___jp_1802_;
}
else
{
if (v___y_1837_ == 0)
{
v___y_1803_ = v___y_1833_;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1846_;
v___y_1806_ = v_argsArray_1841_;
v___y_1807_ = v___y_1835_;
v___y_1808_ = v___y_1838_;
v___y_1809_ = v___y_1849_;
v___y_1810_ = v___y_1839_;
v___y_1811_ = v___y_1845_;
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___y_1840_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___y_1848_;
v___y_1816_ = v___y_1836_;
v___y_1817_ = v___y_1837_;
v___y_1818_ = v___y_1842_;
v___y_1819_ = v___y_1847_;
v___y_1820_ = v___y_1837_;
goto v___jp_1802_;
}
else
{
lean_object* v_ref_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 5);
v___x_1852_ = 0;
v___x_1853_ = l_Lean_SourceInfo_fromRef(v_ref_1851_, v___x_1852_);
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_1855_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1854_);
v___x_1856_ = l_Lean_SourceInfo_fromRef(v_tk_1230_, v___x_1214_);
v___x_1857_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1860_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1838_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1862_; 
v_val_1861_ = lean_ctor_get(v___y_1838_, 0);
lean_inc(v_val_1861_);
v___x_1862_ = l_Array_mkArray1___redArg(v_val_1861_);
v___y_1670_ = v___y_1833_;
v___y_1671_ = v___y_1834_;
v___y_1672_ = v___y_1846_;
v___y_1673_ = v___x_1853_;
v___y_1674_ = v_argsArray_1841_;
v___y_1675_ = v___y_1835_;
v___y_1676_ = v___x_1858_;
v___y_1677_ = v___y_1838_;
v___y_1678_ = v___y_1849_;
v___y_1679_ = v___y_1839_;
v___y_1680_ = v___x_1860_;
v___y_1681_ = v___y_1845_;
v___y_1682_ = v___y_1844_;
v___y_1683_ = v___y_1840_;
v___y_1684_ = v___x_1859_;
v___y_1685_ = v___y_1843_;
v___y_1686_ = v___y_1848_;
v___y_1687_ = v___y_1836_;
v___y_1688_ = v___y_1837_;
v___y_1689_ = v___x_1855_;
v___y_1690_ = v___y_1847_;
v___y_1691_ = v___y_1842_;
v___y_1692_ = v___x_1862_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1670_ = v___y_1833_;
v___y_1671_ = v___y_1834_;
v___y_1672_ = v___y_1846_;
v___y_1673_ = v___x_1853_;
v___y_1674_ = v_argsArray_1841_;
v___y_1675_ = v___y_1835_;
v___y_1676_ = v___x_1858_;
v___y_1677_ = v___y_1838_;
v___y_1678_ = v___y_1849_;
v___y_1679_ = v___y_1839_;
v___y_1680_ = v___x_1860_;
v___y_1681_ = v___y_1845_;
v___y_1682_ = v___y_1844_;
v___y_1683_ = v___y_1840_;
v___y_1684_ = v___x_1859_;
v___y_1685_ = v___y_1843_;
v___y_1686_ = v___y_1848_;
v___y_1687_ = v___y_1836_;
v___y_1688_ = v___y_1837_;
v___y_1689_ = v___x_1855_;
v___y_1690_ = v___y_1847_;
v___y_1691_ = v___y_1842_;
v___y_1692_ = v___x_1863_;
goto v___jp_1669_;
}
}
}
}
v___jp_1864_:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1881_, v___y_1877_, v___y_1871_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = l_Lean_LibrarySuggestions_select(v_a_1884_, v___y_1882_, v___y_1877_, v___y_1871_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_sz_1887_ = lean_array_size(v_a_1886_);
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1886_, v_sz_1887_, v___x_1888_, v___y_1866_, v___y_1880_, v___y_1881_, v___y_1868_, v___y_1870_, v___y_1877_, v___y_1871_, v___y_1875_, v___y_1876_);
lean_dec(v_a_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___y_1833_ = v___y_1865_;
v___y_1834_ = v___y_1867_;
v___y_1835_ = v___y_1869_;
v___y_1836_ = v___y_1878_;
v___y_1837_ = v___y_1879_;
v___y_1838_ = v___y_1872_;
v___y_1839_ = v___y_1873_;
v___y_1840_ = v___y_1874_;
v_argsArray_1841_ = v_a_1890_;
v___y_1842_ = v___y_1880_;
v___y_1843_ = v___y_1881_;
v___y_1844_ = v___y_1868_;
v___y_1845_ = v___y_1870_;
v___y_1846_ = v___y_1877_;
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1875_;
v___y_1849_ = v___y_1876_;
goto v___jp_1832_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v___y_1878_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1869_);
lean_dec(v___y_1865_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1891_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1889_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1889_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v___y_1878_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1899_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1885_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1885_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1878_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1907_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1883_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1883_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
v___jp_1915_:
{
lean_object* v_config_1934_; uint8_t v_suggestions_1935_; 
v_config_1934_ = lean_ctor_get(v___y_1929_, 0);
lean_inc_ref(v_config_1934_);
lean_dec_ref(v___y_1929_);
v_suggestions_1935_ = lean_ctor_get_uint8(v_config_1934_, sizeof(void*)*3 + 26);
if (v_suggestions_1935_ == 0)
{
lean_dec_ref(v_config_1934_);
lean_dec_ref(v___f_1218_);
v___y_1833_ = v___y_1916_;
v___y_1834_ = v___y_1917_;
v___y_1835_ = v___y_1919_;
v___y_1836_ = v___y_1928_;
v___y_1837_ = v___y_1930_;
v___y_1838_ = v___y_1922_;
v___y_1839_ = v___y_1923_;
v___y_1840_ = v___y_1924_;
v_argsArray_1841_ = v___y_1933_;
v___y_1842_ = v___y_1931_;
v___y_1843_ = v___y_1932_;
v___y_1844_ = v___y_1918_;
v___y_1845_ = v___y_1920_;
v___y_1846_ = v___y_1927_;
v___y_1847_ = v___y_1921_;
v___y_1848_ = v___y_1925_;
v___y_1849_ = v___y_1926_;
goto v___jp_1832_;
}
else
{
lean_object* v_maxSuggestions_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_maxSuggestions_1936_ = lean_ctor_get(v_config_1934_, 2);
lean_inc(v_maxSuggestions_1936_);
lean_dec_ref(v_config_1934_);
v___x_1937_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1938_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1936_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(100u);
v___x_1940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1937_);
lean_ctor_set(v___x_1940_, 2, v___f_1218_);
lean_ctor_set(v___x_1940_, 3, v___x_1938_);
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1933_;
v___y_1867_ = v___y_1917_;
v___y_1868_ = v___y_1918_;
v___y_1869_ = v___y_1919_;
v___y_1870_ = v___y_1920_;
v___y_1871_ = v___y_1921_;
v___y_1872_ = v___y_1922_;
v___y_1873_ = v___y_1923_;
v___y_1874_ = v___y_1924_;
v___y_1875_ = v___y_1925_;
v___y_1876_ = v___y_1926_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1928_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___x_1940_;
goto v___jp_1864_;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; 
v_val_1941_ = lean_ctor_get(v_maxSuggestions_1936_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_maxSuggestions_1936_, 1);
v___x_1942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1942_, 0, v_val_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1937_);
lean_ctor_set(v___x_1942_, 2, v___f_1218_);
lean_ctor_set(v___x_1942_, 3, v___x_1938_);
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1933_;
v___y_1867_ = v___y_1917_;
v___y_1868_ = v___y_1918_;
v___y_1869_ = v___y_1919_;
v___y_1870_ = v___y_1920_;
v___y_1871_ = v___y_1921_;
v___y_1872_ = v___y_1922_;
v___y_1873_ = v___y_1923_;
v___y_1874_ = v___y_1924_;
v___y_1875_ = v___y_1925_;
v___y_1876_ = v___y_1926_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1928_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___x_1942_;
goto v___jp_1864_;
}
}
}
v___jp_1943_:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = 0;
lean_inc(v___y_1947_);
v___x_1960_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1947_, v___x_1959_, v___y_1957_, v___y_1946_, v___y_1945_);
if (lean_obj_tag(v___x_1960_) == 0)
{
if (lean_obj_tag(v___y_1944_) == 1)
{
lean_object* v_a_1961_; lean_object* v_val_1962_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v_val_1962_ = lean_ctor_get(v___y_1944_, 0);
lean_inc(v_val_1962_);
lean_dec_ref_known(v___y_1944_, 1);
v___x_1963_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1962_);
lean_dec(v_val_1962_);
lean_inc(v___y_1953_);
v___y_1916_ = v___y_1953_;
v___y_1917_ = v___x_1959_;
v___y_1918_ = v___y_1950_;
v___y_1919_ = v___y_1954_;
v___y_1920_ = v___y_1951_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1958_;
v___y_1923_ = v___y_1953_;
v___y_1924_ = v___y_1947_;
v___y_1925_ = v___y_1946_;
v___y_1926_ = v___y_1945_;
v___y_1927_ = v___y_1952_;
v___y_1928_ = v___y_1949_;
v___y_1929_ = v_a_1961_;
v___y_1930_ = v___y_1955_;
v___y_1931_ = v___y_1957_;
v___y_1932_ = v___y_1956_;
v___y_1933_ = v___x_1963_;
goto v___jp_1915_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1965_; 
lean_dec(v___y_1944_);
v_a_1964_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1965_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1953_);
v___y_1916_ = v___y_1953_;
v___y_1917_ = v___x_1959_;
v___y_1918_ = v___y_1950_;
v___y_1919_ = v___y_1954_;
v___y_1920_ = v___y_1951_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1958_;
v___y_1923_ = v___y_1953_;
v___y_1924_ = v___y_1947_;
v___y_1925_ = v___y_1946_;
v___y_1926_ = v___y_1945_;
v___y_1927_ = v___y_1952_;
v___y_1928_ = v___y_1949_;
v___y_1929_ = v_a_1964_;
v___y_1930_ = v___y_1955_;
v___y_1931_ = v___y_1957_;
v___y_1932_ = v___y_1956_;
v___y_1933_ = v___x_1965_;
goto v___jp_1915_;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v___y_1958_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec(v___y_1949_);
lean_dec(v___y_1947_);
lean_dec(v___y_1944_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v_a_1966_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1960_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
v___jp_1974_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Syntax_getOptional_x3f(v___y_1978_);
lean_dec(v___y_1978_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_box(0);
v___y_1944_ = v___y_1980_;
v___y_1945_ = v___y_1983_;
v___y_1946_ = v___y_1982_;
v___y_1947_ = v___y_1981_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1984_;
v___y_1950_ = v___y_1975_;
v___y_1951_ = v___y_1977_;
v___y_1952_ = v___y_1985_;
v___y_1953_ = v___y_1989_;
v___y_1954_ = v___y_1976_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___y_1988_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___x_1991_;
goto v___jp_1943_;
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1990_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v___x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_val_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v___y_1944_ = v___y_1980_;
v___y_1945_ = v___y_1983_;
v___y_1946_ = v___y_1982_;
v___y_1947_ = v___y_1981_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1984_;
v___y_1950_ = v___y_1975_;
v___y_1951_ = v___y_1977_;
v___y_1952_ = v___y_1985_;
v___y_1953_ = v___y_1989_;
v___y_1954_ = v___y_1976_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___y_1988_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___x_1997_;
goto v___jp_1943_;
}
}
}
}
v___jp_2000_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(4u);
v___x_2017_ = l_Lean_Syntax_getArg(v___y_2002_, v___x_2016_);
lean_dec(v___y_2002_);
v___x_2018_ = l_Lean_Syntax_getOptional_x3f(v___x_2017_);
lean_dec(v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
v___y_1975_ = v___y_2010_;
v___y_1976_ = v___y_2001_;
v___y_1977_ = v___y_2011_;
v___y_1978_ = v___y_2003_;
v___y_1979_ = v___y_2013_;
v___y_1980_ = v_args_2007_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___y_2014_;
v___y_1983_ = v___y_2015_;
v___y_1984_ = v___y_2004_;
v___y_1985_ = v___y_2012_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2008_;
v___y_1988_ = v___y_2009_;
v___y_1989_ = v___x_2019_;
goto v___jp_1974_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v___y_1975_ = v___y_2010_;
v___y_1976_ = v___y_2001_;
v___y_1977_ = v___y_2011_;
v___y_1978_ = v___y_2003_;
v___y_1979_ = v___y_2013_;
v___y_1980_ = v_args_2007_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___y_2014_;
v___y_1983_ = v___y_2015_;
v___y_1984_ = v___y_2004_;
v___y_1985_ = v___y_2012_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2008_;
v___y_1988_ = v___y_2009_;
v___y_1989_ = v___x_2025_;
goto v___jp_1974_;
}
}
}
}
v___jp_2029_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_unsigned_to_nat(3u);
v___x_2045_ = l_Lean_Syntax_getArg(v___y_2031_, v___x_2044_);
v___x_2046_ = l_Lean_Syntax_isNone(v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; 
lean_inc(v___x_2045_);
v___x_2047_ = l_Lean_Syntax_matchesNull(v___x_2045_, v___x_2028_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v___x_2045_);
lean_dec(v_o_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2049_ = l_Lean_Syntax_getArg(v___x_2045_, v___x_1229_);
lean_dec(v___x_2045_);
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2051_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2050_);
lean_inc(v___x_2049_);
v___x_2052_ = l_Lean_Syntax_isOfKind(v___x_2049_, v___x_2051_);
lean_dec(v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec(v___x_2049_);
lean_dec(v_o_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2053_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v_args_2055_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_Syntax_getArg(v___x_2049_, v___x_2028_);
lean_dec(v___x_2049_);
v_args_2055_ = l_Lean_Syntax_getArgs(v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_args_2055_);
v___y_2001_ = v_o_2035_;
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___y_2030_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
v_args_2007_ = v___x_2056_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
goto v___jp_2000_;
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v___x_2045_);
v___x_2057_ = lean_box(0);
v___y_2001_ = v_o_2035_;
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___y_2030_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
v_args_2007_ = v___x_2057_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
goto v___jp_2000_;
}
}
v___jp_2058_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = l_Lean_Syntax_getArg(v_stx_1213_, v___x_2068_);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2071_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2070_);
lean_inc(v___x_2069_);
v___x_2072_ = l_Lean_Syntax_isOfKind(v___x_2069_, v___x_2071_);
lean_dec(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2073_;
}
else
{
lean_object* v_cfg_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_cfg_2074_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_1229_);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
lean_inc_ref(v___x_1215_);
v___x_2076_ = l_Lean_Name_mkStr4(v___x_1215_, v___x_1216_, v___x_1217_, v___x_2075_);
lean_inc(v_cfg_2074_);
v___x_2077_ = l_Lean_Syntax_isOfKind(v_cfg_2074_, v___x_2076_);
lean_dec(v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_cfg_2074_);
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2028_);
v___x_2080_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2068_);
v___x_2081_ = l_Lean_Syntax_isNone(v___x_2080_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
lean_inc(v___x_2080_);
v___x_2082_ = l_Lean_Syntax_matchesNull(v___x_2080_, v___x_2028_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec(v___x_2080_);
lean_dec(v___x_2079_);
lean_dec(v_cfg_2074_);
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1230_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v___x_1215_);
v___x_2083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2083_;
}
else
{
lean_object* v_o_2084_; lean_object* v___x_2085_; 
v_o_2084_ = l_Lean_Syntax_getArg(v___x_2080_, v___x_1229_);
lean_dec(v___x_2080_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_o_2084_);
v___y_2030_ = v___x_2079_;
v___y_2031_ = v___x_2069_;
v___y_2032_ = v_bang_2059_;
v___y_2033_ = v___x_2077_;
v___y_2034_ = v_cfg_2074_;
v_o_2035_ = v___x_2085_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
goto v___jp_2029_;
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v___x_2080_);
v___x_2086_ = lean_box(0);
v___y_2030_ = v___x_2079_;
v___y_2031_ = v___x_2069_;
v___y_2032_ = v_bang_2059_;
v___y_2033_ = v___x_2077_;
v___y_2034_ = v_cfg_2074_;
v_o_2035_ = v___x_2086_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
goto v___jp_2029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2094_, lean_object* v_stx_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___f_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v___x_40466__boxed_2110_; uint8_t v___x_40467__boxed_2111_; lean_object* v_res_2112_; 
v___x_40466__boxed_2110_ = lean_unbox(v___x_2094_);
v___x_40467__boxed_2111_ = lean_unbox(v___x_2096_);
v_res_2112_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40466__boxed_2110_, v_stx_2095_, v___x_40467__boxed_2111_, v___x_2097_, v___x_2098_, v___x_2099_, v___f_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_stx_2095_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___f_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___y_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2122_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v_stx_2122_, v___x_2135_);
v___x_2137_ = 1;
v___f_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2139_ = lean_box(v___x_2136_);
v___x_2140_ = lean_box(v___x_2137_);
v___y_2141_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2141_, 0, v___x_2139_);
lean_closure_set(v___y_2141_, 1, v_stx_2122_);
lean_closure_set(v___y_2141_, 2, v___x_2140_);
lean_closure_set(v___y_2141_, 3, v___x_2132_);
lean_closure_set(v___y_2141_, 4, v___x_2133_);
lean_closure_set(v___y_2141_, 5, v___x_2134_);
lean_closure_set(v___y_2141_, 6, v___f_2138_);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2142_, 0, v___y_2141_);
v___x_2143_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2142_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2155_, lean_object* v_as_2156_, lean_object* v_as_x27_2157_, lean_object* v_b_2158_, lean_object* v_a_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2155_, v_as_x27_2157_, v_b_2158_, v___y_2166_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2170_, lean_object* v_as_2171_, lean_object* v_as_x27_2172_, lean_object* v_b_2173_, lean_object* v_a_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2170_, v_as_2171_, v_as_x27_2172_, v_b_2173_, v_a_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v_as_x27_2172_);
lean_dec(v_as_2171_);
lean_dec(v___x_2170_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2185_, lean_object* v_ref_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_ref_2199_, lean_object* v_msg_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2198_, v_ref_2199_, v_msg_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_ref_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2211_, lean_object* v_ref_2212_, lean_object* v_constName_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2212_, v_constName_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_ref_2225_, lean_object* v_constName_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2224_, v_ref_2225_, v_constName_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_ref_2225_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2238_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_msg_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2249_, v_msg_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2261_, v___y_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_opt_2272_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2283_, lean_object* v_ref_2284_, lean_object* v_msg_2285_, lean_object* v_declHint_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2284_, v_msg_2285_, v_declHint_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_ref_2298_, lean_object* v_msg_2299_, lean_object* v_declHint_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2297_, v_ref_2298_, v_msg_2299_, v_declHint_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v_ref_2298_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2311_, lean_object* v_declHint_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2311_, v_declHint_2312_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2323_, lean_object* v_declHint_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2335_, lean_object* v_msgData_2336_, uint8_t v_severity_2337_, uint8_t v_isSilent_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2335_, v_msgData_2336_, v_severity_2337_, v_isSilent_2338_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2349_, lean_object* v_msgData_2350_, lean_object* v_severity_2351_, lean_object* v_isSilent_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v_severity_boxed_2362_; uint8_t v_isSilent_boxed_2363_; lean_object* v_res_2364_; 
v_severity_boxed_2362_ = lean_unbox(v_severity_2351_);
v_isSilent_boxed_2363_ = lean_unbox(v_isSilent_2352_);
v_res_2364_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2349_, v_msgData_2350_, v_severity_boxed_2362_, v_isSilent_boxed_2363_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v_ref_2349_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2372_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2375_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2372_, v___x_2373_, v___x_2374_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2407_ = l_Lean_addBuiltinDeclarationRanges(v___x_2405_, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2410_, lean_object* v_as_x27_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_){
_start:
{
if (lean_obj_tag(v_as_x27_2411_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_b_2412_);
return v___x_2415_;
}
else
{
lean_object* v_head_2416_; lean_object* v_tail_2417_; lean_object* v_ref_2418_; uint8_t v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_head_2416_ = lean_ctor_get(v_as_x27_2411_, 0);
v_tail_2417_ = lean_ctor_get(v_as_x27_2411_, 1);
v_ref_2418_ = lean_ctor_get(v___y_2413_, 5);
v___x_2419_ = 1;
v___x_2420_ = 0;
v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2418_, v___x_2420_);
v___x_2422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2423_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2424_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2421_);
v___x_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2421_);
lean_ctor_set(v___x_2425_, 1, v___x_2423_);
lean_ctor_set(v___x_2425_, 2, v___x_2424_);
lean_inc(v_head_2416_);
v___x_2426_ = l_Lean_mkCIdentFrom(v___x_2410_, v_head_2416_, v___x_2419_);
lean_inc_ref(v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node3(v___x_2421_, v___x_2422_, v___x_2425_, v___x_2425_, v___x_2426_);
v___x_2428_ = lean_array_push(v_b_2412_, v___x_2427_);
v_as_x27_2411_ = v_tail_2417_;
v_b_2412_ = v___x_2428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2430_, lean_object* v_as_x27_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2430_, v_as_x27_2431_, v_b_2432_, v___y_2433_);
lean_dec_ref(v___y_2433_);
lean_dec(v_as_x27_2431_);
lean_dec(v___x_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_b_2439_);
return v___x_2450_;
}
else
{
lean_object* v_a_2451_; lean_object* v_name_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2451_ = lean_array_uget_borrowed(v_as_2436_, v_i_2438_);
v_name_2452_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_name_2452_);
v___x_2453_ = lean_mk_syntax_ident(v_name_2452_);
lean_inc(v___x_2453_);
v___x_2454_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2453_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2453_, v_a_2455_, v_b_2439_, v___y_2446_);
lean_dec(v_a_2455_);
lean_dec(v___x_2453_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; size_t v___x_2458_; size_t v___x_2459_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2438_, v___x_2458_);
v_i_2438_ = v___x_2459_;
v_b_2439_ = v_a_2457_;
goto _start;
}
else
{
return v___x_2456_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v___x_2453_);
lean_dec_ref(v_b_2439_);
v_a_2461_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2454_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2454_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2469_, lean_object* v_sz_2470_, lean_object* v_i_2471_, lean_object* v_b_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2470_);
lean_dec(v_sz_2470_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2469_, v_sz_boxed_2482_, v_i_boxed_2483_, v_b_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_as_2469_);
return v_res_2484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_unsigned_to_nat(32u);
v___x_2492_ = lean_mk_empty_array_with_capacity(v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2494_ = ((size_t)5ULL);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_unsigned_to_nat(32u);
v___x_2497_ = lean_mk_empty_array_with_capacity(v___x_2496_);
v___x_2498_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2499_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2495_);
lean_ctor_set(v___x_2499_, 3, v___x_2495_);
lean_ctor_set_usize(v___x_2499_, 4, v___x_2494_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
lean_ctor_set(v___x_2502_, 3, v___x_2500_);
return v___x_2502_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2504_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___x_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2514_, lean_object* v_stx_2515_, uint8_t v___x_2516_, lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v___f_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
if (v___x_2514_ == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_2530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v_tk_2532_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2647_; uint8_t v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v_stxForSuggestion_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; uint8_t v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; uint8_t v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; uint8_t v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; uint8_t v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; uint8_t v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2861_; uint8_t v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; uint8_t v___y_2944_; lean_object* v___y_2945_; uint8_t v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; uint8_t v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; uint8_t v___y_2990_; uint8_t v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_stxForExecution_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3022_; lean_object* v___y_3023_; uint8_t v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3049_; uint8_t v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3079_; uint8_t v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3179_; uint8_t v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3266_; uint8_t v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; uint8_t v___y_3340_; uint8_t v___y_3341_; lean_object* v___y_3342_; lean_object* v_argsArray_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3369_; uint8_t v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; uint8_t v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v_args_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___x_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; uint8_t v___y_3503_; lean_object* v___y_3504_; lean_object* v_o_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v_bang_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v_tk_2532_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_2531_);
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3557_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_3498_);
v___x_3558_ = l_Lean_Syntax_isNone(v___x_3557_);
if (v___x_3558_ == 0)
{
uint8_t v___x_3559_; 
lean_inc(v___x_3557_);
v___x_3559_ = l_Lean_Syntax_matchesNull(v___x_3557_, v___x_3498_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
lean_dec(v___x_3557_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3560_;
}
else
{
lean_object* v_bang_3561_; lean_object* v___x_3562_; 
v_bang_3561_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_2531_);
lean_dec(v___x_3557_);
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_bang_3561_);
v_bang_3529_ = v___x_3562_;
v___y_3530_ = v___y_2521_;
v___y_3531_ = v___y_2522_;
v___y_3532_ = v___y_2523_;
v___y_3533_ = v___y_2524_;
v___y_3534_ = v___y_2525_;
v___y_3535_ = v___y_2526_;
v___y_3536_ = v___y_2527_;
v___y_3537_ = v___y_2528_;
goto v___jp_3528_;
}
}
else
{
lean_object* v___x_3563_; 
lean_dec(v___x_3557_);
v___x_3563_ = lean_box(0);
v_bang_3529_ = v___x_3563_;
v___y_3530_ = v___y_2521_;
v___y_3531_ = v___y_2522_;
v___y_3532_ = v___y_2523_;
v___y_3533_ = v___y_2524_;
v___y_3534_ = v___y_2525_;
v___y_3535_ = v___y_2526_;
v___y_3536_ = v___y_2527_;
v___y_3537_ = v___y_2528_;
goto v___jp_3528_;
}
v___jp_2533_:
{
lean_object* v_usedTheorems_2540_; lean_object* v_diag_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2583_; 
v_usedTheorems_2540_ = lean_ctor_get(v___y_2534_, 0);
v_diag_2541_ = lean_ctor_get(v___y_2534_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___y_2534_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2543_ = v___y_2534_;
v_isShared_2544_ = v_isSharedCheck_2583_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_diag_2541_);
lean_inc(v_usedTheorems_2540_);
lean_dec(v___y_2534_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2583_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2535_, v_usedTheorems_2540_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v_usedTheorems_2540_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v_ref_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v_ref_2547_ = lean_ctor_get(v___y_2538_, 5);
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v_a_2546_);
lean_ctor_set(v___x_2543_, 0, v___x_2548_);
v___x_2550_ = v___x_2543_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_a_2546_);
v___x_2550_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_ctor_set(v___x_2552_, 2, v___x_2551_);
lean_ctor_set(v___x_2552_, 3, v___x_2551_);
lean_ctor_set(v___x_2552_, 4, v___x_2551_);
lean_ctor_set(v___x_2552_, 5, v___x_2551_);
lean_inc(v_ref_2547_);
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_ref_2547_);
v___x_2554_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2555_ = 4;
v___x_2556_ = l_Lean_MessageData_nil;
v___x_2557_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2532_, v___x_2552_, v___x_2553_, v___x_2554_, v___x_2551_, v___x_2555_, v___x_2556_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2565_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_diag_2541_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_diag_2541_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_diag_2541_);
v_a_2566_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2557_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2557_);
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
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_diag_2541_);
lean_dec(v_tk_2532_);
v_a_2575_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2545_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2545_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
v___jp_2584_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2585_, v___y_2591_, v___y_2587_, v___y_2589_, v___y_2588_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2596_ = l_Lean_Meta_simpAll(v_a_2594_, v___y_2592_, v___y_2586_, v___x_2595_, v___y_2591_, v___y_2587_, v___y_2589_, v___y_2588_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_fst_2598_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v_fst_2598_ = lean_ctor_get(v_a_2597_, 0);
if (lean_obj_tag(v_fst_2598_) == 0)
{
lean_object* v_snd_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_snd_2599_ = lean_ctor_get(v_a_2597_, 1);
lean_inc(v_snd_2599_);
lean_dec(v_a_2597_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2600_, v___y_2585_, v___y_2591_, v___y_2587_, v___y_2589_, v___y_2588_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref_known(v___x_2601_, 1);
v___y_2534_ = v_snd_2599_;
v___y_2535_ = v___y_2590_;
v___y_2536_ = v___y_2591_;
v___y_2537_ = v___y_2587_;
v___y_2538_ = v___y_2589_;
v___y_2539_ = v___y_2588_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_snd_2599_);
lean_dec(v___y_2590_);
lean_dec(v_tk_2532_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2628_; 
lean_inc_ref(v_fst_2598_);
v_snd_2610_ = lean_ctor_get(v_a_2597_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2597_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v_a_2597_, 0);
lean_dec(v_unused_2629_);
v___x_2612_ = v_a_2597_;
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_dec(v_a_2597_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v_val_2614_ = lean_ctor_get(v_fst_2598_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v_fst_2598_, 1);
v___x_2615_ = lean_box(0);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 1, v___x_2615_);
lean_ctor_set(v___x_2612_, 0, v_val_2614_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_val_2614_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2617_, v___y_2585_, v___y_2591_, v___y_2587_, v___y_2589_, v___y_2588_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_dec_ref_known(v___x_2618_, 1);
v___y_2534_ = v_snd_2610_;
v___y_2535_ = v___y_2590_;
v___y_2536_ = v___y_2591_;
v___y_2537_ = v___y_2587_;
v___y_2538_ = v___y_2589_;
v___y_2539_ = v___y_2588_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_snd_2610_);
lean_dec(v___y_2590_);
lean_dec(v_tk_2532_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
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
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v___y_2590_);
lean_dec(v_tk_2532_);
v_a_2630_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2596_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2596_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2586_);
lean_dec(v_tk_2532_);
v_a_2638_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2593_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2593_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
v___jp_2646_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2661_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2650_, v___x_2516_, v___y_2648_, v___x_2516_, v___x_2660_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2650_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
if (lean_obj_tag(v___y_2647_) == 0)
{
lean_object* v_ctx_2663_; lean_object* v_simprocs_2664_; 
v_ctx_2663_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2663_);
v_simprocs_2664_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2664_);
lean_dec(v_a_2662_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v_simprocs_2664_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2659_;
v___y_2589_ = v___y_2658_;
v___y_2590_ = v_stxForSuggestion_2651_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v_ctx_2663_;
goto v___jp_2584_;
}
else
{
lean_dec_ref_known(v___y_2647_, 1);
if (v___y_2649_ == 0)
{
lean_object* v_ctx_2665_; lean_object* v_simprocs_2666_; 
v_ctx_2665_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2665_);
v_simprocs_2666_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2666_);
lean_dec(v_a_2662_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v_simprocs_2666_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2659_;
v___y_2589_ = v___y_2658_;
v___y_2590_ = v_stxForSuggestion_2651_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v_ctx_2665_;
goto v___jp_2584_;
}
else
{
lean_object* v_ctx_2667_; lean_object* v_simprocs_2668_; lean_object* v___x_2669_; 
v_ctx_2667_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2667_);
v_simprocs_2668_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2668_);
lean_dec(v_a_2662_);
v___x_2669_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2667_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v_simprocs_2668_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2659_;
v___y_2589_ = v___y_2658_;
v___y_2590_ = v_stxForSuggestion_2651_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v___x_2669_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_stxForSuggestion_2651_);
lean_dec(v___y_2647_);
lean_dec(v_tk_2532_);
v_a_2670_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2661_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_inc_ref_n(v___y_2683_, 2);
v___x_2699_ = l_Array_append___redArg(v___y_2683_, v___y_2698_);
lean_dec_ref(v___y_2698_);
lean_inc_n(v___y_2682_, 2);
lean_inc_n(v___y_2697_, 2);
v___x_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___y_2697_);
lean_ctor_set(v___x_2700_, 1, v___y_2682_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2697_);
lean_ctor_set(v___x_2701_, 1, v___y_2682_);
lean_ctor_set(v___x_2701_, 2, v___y_2683_);
v___x_2702_ = l_Lean_Syntax_node5(v___y_2697_, v___y_2680_, v___y_2691_, v___y_2684_, v___y_2688_, v___x_2700_, v___x_2701_);
v___y_2647_ = v___y_2690_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2692_;
v___y_2650_ = v___y_2693_;
v_stxForSuggestion_2651_ = v___x_2702_;
v___y_2652_ = v___y_2687_;
v___y_2653_ = v___y_2694_;
v___y_2654_ = v___y_2689_;
v___y_2655_ = v___y_2685_;
v___y_2656_ = v___y_2686_;
v___y_2657_ = v___y_2696_;
v___y_2658_ = v___y_2681_;
v___y_2659_ = v___y_2695_;
goto v___jp_2646_;
}
v___jp_2703_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_inc_ref(v___y_2709_);
v___x_2724_ = l_Array_append___redArg(v___y_2709_, v___y_2723_);
lean_dec_ref(v___y_2723_);
lean_inc(v___y_2707_);
lean_inc(v___y_2722_);
v___x_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2722_);
lean_ctor_set(v___x_2725_, 1, v___y_2707_);
lean_ctor_set(v___x_2725_, 2, v___x_2724_);
if (lean_obj_tag(v___y_2708_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2726_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v___y_2708_, 1);
v___x_2727_ = l_Lean_SourceInfo_fromRef(v_val_2726_, v___x_2516_);
lean_dec(v_val_2726_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = l_Array_mkArray1___redArg(v___x_2729_);
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___y_2709_;
v___y_2684_ = v___y_2710_;
v___y_2685_ = v___y_2711_;
v___y_2686_ = v___y_2712_;
v___y_2687_ = v___y_2713_;
v___y_2688_ = v___x_2725_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___y_2719_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___x_2730_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v___y_2708_);
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___y_2709_;
v___y_2684_ = v___y_2710_;
v___y_2685_ = v___y_2711_;
v___y_2686_ = v___y_2712_;
v___y_2687_ = v___y_2713_;
v___y_2688_ = v___x_2725_;
v___y_2689_ = v___y_2714_;
v___y_2690_ = v___y_2715_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___y_2719_;
v___y_2694_ = v___y_2718_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___x_2731_;
goto v___jp_2678_;
}
}
v___jp_2732_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_inc_ref_n(v___y_2740_, 2);
v___x_2754_ = l_Array_append___redArg(v___y_2740_, v___y_2753_);
lean_dec_ref(v___y_2753_);
lean_inc_n(v___y_2747_, 3);
lean_inc_n(v___y_2743_, 5);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___y_2743_);
lean_ctor_set(v___x_2755_, 1, v___y_2747_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2743_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2759_ = l_Lean_Syntax_SepArray_ofElems(v___x_2758_, v___y_2741_);
lean_dec_ref(v___y_2741_);
v___x_2760_ = l_Array_append___redArg(v___y_2740_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___y_2743_);
lean_ctor_set(v___x_2761_, 1, v___y_2747_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2743_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_Syntax_node3(v___y_2743_, v___y_2747_, v___x_2757_, v___x_2761_, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node5(v___y_2743_, v___y_2748_, v___y_2734_, v___y_2736_, v___y_2737_, v___x_2755_, v___x_2764_);
v___y_2647_ = v___y_2745_;
v___y_2648_ = v___y_2733_;
v___y_2649_ = v___y_2746_;
v___y_2650_ = v___y_2749_;
v_stxForSuggestion_2651_ = v___x_2765_;
v___y_2652_ = v___y_2742_;
v___y_2653_ = v___y_2750_;
v___y_2654_ = v___y_2744_;
v___y_2655_ = v___y_2738_;
v___y_2656_ = v___y_2739_;
v___y_2657_ = v___y_2752_;
v___y_2658_ = v___y_2735_;
v___y_2659_ = v___y_2751_;
goto v___jp_2646_;
}
v___jp_2766_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc_ref(v___y_2774_);
v___x_2788_ = l_Array_append___redArg(v___y_2774_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_inc(v___y_2782_);
lean_inc(v___y_2777_);
v___x_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___y_2777_);
lean_ctor_set(v___x_2789_, 1, v___y_2782_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
if (lean_obj_tag(v___y_2770_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_val_2790_ = lean_ctor_get(v___y_2770_, 0);
lean_inc(v_val_2790_);
lean_dec_ref_known(v___y_2770_, 1);
v___x_2791_ = l_Lean_SourceInfo_fromRef(v_val_2790_, v___x_2516_);
lean_dec(v_val_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Array_mkArray1___redArg(v___x_2793_);
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2789_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2781_;
v___y_2749_ = v___y_2784_;
v___y_2750_ = v___y_2783_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2794_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2795_; 
lean_dec(v___y_2770_);
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2789_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2781_;
v___y_2749_ = v___y_2784_;
v___y_2750_ = v___y_2783_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2795_;
goto v___jp_2732_;
}
}
v___jp_2796_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc_ref_n(v___y_2799_, 2);
v___x_2818_ = l_Array_append___redArg(v___y_2799_, v___y_2817_);
lean_dec_ref(v___y_2817_);
lean_inc_n(v___y_2800_, 3);
lean_inc_n(v___y_2814_, 5);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___y_2814_);
lean_ctor_set(v___x_2819_, 1, v___y_2800_);
lean_ctor_set(v___x_2819_, 2, v___x_2818_);
v___x_2820_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___y_2814_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2823_ = l_Lean_Syntax_SepArray_ofElems(v___x_2822_, v___y_2805_);
lean_dec_ref(v___y_2805_);
v___x_2824_ = l_Array_append___redArg(v___y_2799_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2825_, 0, v___y_2814_);
lean_ctor_set(v___x_2825_, 1, v___y_2800_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___y_2814_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_Syntax_node3(v___y_2814_, v___y_2800_, v___x_2821_, v___x_2825_, v___x_2827_);
v___x_2829_ = l_Lean_Syntax_node5(v___y_2814_, v___y_2809_, v___y_2816_, v___y_2802_, v___y_2801_, v___x_2819_, v___x_2828_);
v___y_2647_ = v___y_2808_;
v___y_2648_ = v___y_2797_;
v___y_2649_ = v___y_2810_;
v___y_2650_ = v___y_2811_;
v_stxForSuggestion_2651_ = v___x_2829_;
v___y_2652_ = v___y_2806_;
v___y_2653_ = v___y_2812_;
v___y_2654_ = v___y_2807_;
v___y_2655_ = v___y_2803_;
v___y_2656_ = v___y_2804_;
v___y_2657_ = v___y_2815_;
v___y_2658_ = v___y_2798_;
v___y_2659_ = v___y_2813_;
goto v___jp_2646_;
}
v___jp_2830_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_inc_ref(v___y_2833_);
v___x_2852_ = l_Array_append___redArg(v___y_2833_, v___y_2851_);
lean_dec_ref(v___y_2851_);
lean_inc(v___y_2834_);
lean_inc(v___y_2848_);
v___x_2853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2848_);
lean_ctor_set(v___x_2853_, 1, v___y_2834_);
lean_ctor_set(v___x_2853_, 2, v___x_2852_);
if (lean_obj_tag(v___y_2835_) == 1)
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_val_2854_ = lean_ctor_get(v___y_2835_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___y_2835_, 1);
v___x_2855_ = l_Lean_SourceInfo_fromRef(v_val_2854_, v___x_2516_);
lean_dec(v_val_2854_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Array_mkArray1___redArg(v___x_2857_);
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2832_;
v___y_2799_ = v___y_2833_;
v___y_2800_ = v___y_2834_;
v___y_2801_ = v___x_2853_;
v___y_2802_ = v___y_2836_;
v___y_2803_ = v___y_2837_;
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___y_2842_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2846_;
v___y_2812_ = v___y_2845_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___y_2848_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___y_2849_;
v___y_2817_ = v___x_2858_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v___y_2835_);
v___x_2859_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2832_;
v___y_2799_ = v___y_2833_;
v___y_2800_ = v___y_2834_;
v___y_2801_ = v___x_2853_;
v___y_2802_ = v___y_2836_;
v___y_2803_ = v___y_2837_;
v___y_2804_ = v___y_2838_;
v___y_2805_ = v___y_2839_;
v___y_2806_ = v___y_2840_;
v___y_2807_ = v___y_2841_;
v___y_2808_ = v___y_2842_;
v___y_2809_ = v___y_2843_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2846_;
v___y_2812_ = v___y_2845_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___y_2848_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___y_2849_;
v___y_2817_ = v___x_2859_;
goto v___jp_2796_;
}
}
v___jp_2860_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref_n(v___y_2875_, 2);
v___x_2881_ = l_Array_append___redArg(v___y_2875_, v___y_2880_);
lean_dec_ref(v___y_2880_);
lean_inc_n(v___y_2865_, 2);
lean_inc_n(v___y_2864_, 2);
v___x_2882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2882_, 0, v___y_2864_);
lean_ctor_set(v___x_2882_, 1, v___y_2865_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2864_);
lean_ctor_set(v___x_2883_, 1, v___y_2865_);
lean_ctor_set(v___x_2883_, 2, v___y_2875_);
v___x_2884_ = l_Lean_Syntax_node5(v___y_2864_, v___y_2871_, v___y_2870_, v___y_2866_, v___y_2861_, v___x_2882_, v___x_2883_);
v___y_2647_ = v___y_2873_;
v___y_2648_ = v___y_2862_;
v___y_2649_ = v___y_2874_;
v___y_2650_ = v___y_2876_;
v_stxForSuggestion_2651_ = v___x_2884_;
v___y_2652_ = v___y_2869_;
v___y_2653_ = v___y_2877_;
v___y_2654_ = v___y_2872_;
v___y_2655_ = v___y_2867_;
v___y_2656_ = v___y_2868_;
v___y_2657_ = v___y_2879_;
v___y_2658_ = v___y_2863_;
v___y_2659_ = v___y_2878_;
goto v___jp_2646_;
}
v___jp_2885_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_inc_ref(v___y_2900_);
v___x_2906_ = l_Array_append___redArg(v___y_2900_, v___y_2905_);
lean_dec_ref(v___y_2905_);
lean_inc(v___y_2890_);
lean_inc(v___y_2889_);
v___x_2907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2907_, 0, v___y_2889_);
lean_ctor_set(v___x_2907_, 1, v___y_2890_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
if (lean_obj_tag(v___y_2888_) == 1)
{
lean_object* v_val_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_val_2908_ = lean_ctor_get(v___y_2888_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v___y_2888_, 1);
v___x_2909_ = l_Lean_SourceInfo_fromRef(v_val_2908_, v___x_2516_);
lean_dec(v_val_2908_);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Array_mkArray1___redArg(v___x_2911_);
v___y_2861_ = v___x_2907_;
v___y_2862_ = v___y_2886_;
v___y_2863_ = v___y_2887_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2898_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___y_2900_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2901_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2912_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v___y_2888_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2861_ = v___x_2907_;
v___y_2862_ = v___y_2886_;
v___y_2863_ = v___y_2887_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___y_2891_;
v___y_2867_ = v___y_2892_;
v___y_2868_ = v___y_2893_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2898_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___y_2900_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2901_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2913_;
goto v___jp_2860_;
}
}
v___jp_2914_:
{
lean_object* v_ref_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_ref_2931_ = lean_ctor_get(v___y_2917_, 5);
v___x_2932_ = l_Lean_SourceInfo_fromRef(v_ref_2931_, v___y_2930_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2934_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2933_);
v___x_2935_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2936_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2939_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2915_) == 1)
{
lean_object* v_val_2940_; lean_object* v___x_2941_; 
v_val_2940_ = lean_ctor_get(v___y_2915_, 0);
lean_inc(v_val_2940_);
lean_dec_ref_known(v___y_2915_, 1);
v___x_2941_ = l_Array_mkArray1___redArg(v_val_2940_);
v___y_2704_ = v___y_2916_;
v___y_2705_ = v___x_2934_;
v___y_2706_ = v___y_2917_;
v___y_2707_ = v___x_2938_;
v___y_2708_ = v___y_2918_;
v___y_2709_ = v___x_2939_;
v___y_2710_ = v___y_2919_;
v___y_2711_ = v___y_2920_;
v___y_2712_ = v___y_2921_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2937_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2927_;
v___y_2720_ = v___y_2928_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___x_2932_;
v___y_2723_ = v___x_2941_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2942_; 
lean_dec(v___y_2915_);
v___x_2942_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2704_ = v___y_2916_;
v___y_2705_ = v___x_2934_;
v___y_2706_ = v___y_2917_;
v___y_2707_ = v___x_2938_;
v___y_2708_ = v___y_2918_;
v___y_2709_ = v___x_2939_;
v___y_2710_ = v___y_2919_;
v___y_2711_ = v___y_2920_;
v___y_2712_ = v___y_2921_;
v___y_2713_ = v___y_2922_;
v___y_2714_ = v___y_2923_;
v___y_2715_ = v___y_2924_;
v___y_2716_ = v___x_2937_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2927_;
v___y_2720_ = v___y_2928_;
v___y_2721_ = v___y_2929_;
v___y_2722_ = v___x_2932_;
v___y_2723_ = v___x_2942_;
goto v___jp_2703_;
}
}
v___jp_2943_:
{
if (v___y_2961_ == 0)
{
lean_object* v_ref_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_ref_2962_ = lean_ctor_get(v___y_2947_, 5);
v___x_2963_ = l_Lean_SourceInfo_fromRef(v_ref_2962_, v___y_2961_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2965_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2964_);
v___x_2966_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2970_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2945_) == 1)
{
lean_object* v_val_2971_; lean_object* v___x_2972_; 
v_val_2971_ = lean_ctor_get(v___y_2945_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___y_2945_, 1);
v___x_2972_ = l_Array_mkArray1___redArg(v_val_2971_);
v___y_2767_ = v___y_2946_;
v___y_2768_ = v___x_2968_;
v___y_2769_ = v___y_2947_;
v___y_2770_ = v___y_2948_;
v___y_2771_ = v___y_2949_;
v___y_2772_ = v___y_2950_;
v___y_2773_ = v___y_2951_;
v___y_2774_ = v___x_2970_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___y_2953_;
v___y_2777_ = v___x_2963_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___x_2965_;
v___y_2782_ = v___x_2969_;
v___y_2783_ = v___y_2958_;
v___y_2784_ = v___y_2957_;
v___y_2785_ = v___y_2959_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2972_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2973_; 
lean_dec(v___y_2945_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2767_ = v___y_2946_;
v___y_2768_ = v___x_2968_;
v___y_2769_ = v___y_2947_;
v___y_2770_ = v___y_2948_;
v___y_2771_ = v___y_2949_;
v___y_2772_ = v___y_2950_;
v___y_2773_ = v___y_2951_;
v___y_2774_ = v___x_2970_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___y_2953_;
v___y_2777_ = v___x_2963_;
v___y_2778_ = v___y_2954_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___y_2956_;
v___y_2781_ = v___x_2965_;
v___y_2782_ = v___x_2969_;
v___y_2783_ = v___y_2958_;
v___y_2784_ = v___y_2957_;
v___y_2785_ = v___y_2959_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2973_;
goto v___jp_2766_;
}
}
else
{
lean_object* v_ref_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_ref_2974_ = lean_ctor_get(v___y_2947_, 5);
v___x_2975_ = l_Lean_SourceInfo_fromRef(v_ref_2974_, v___y_2944_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2977_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2976_);
v___x_2978_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2982_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2945_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; 
v_val_2983_ = lean_ctor_get(v___y_2945_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v___y_2945_, 1);
v___x_2984_ = l_Array_mkArray1___redArg(v_val_2983_);
v___y_2831_ = v___y_2946_;
v___y_2832_ = v___y_2947_;
v___y_2833_ = v___x_2982_;
v___y_2834_ = v___x_2981_;
v___y_2835_ = v___y_2948_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___y_2950_;
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2954_;
v___y_2842_ = v___y_2955_;
v___y_2843_ = v___x_2977_;
v___y_2844_ = v___y_2956_;
v___y_2845_ = v___y_2958_;
v___y_2846_ = v___y_2957_;
v___y_2847_ = v___y_2959_;
v___y_2848_ = v___x_2975_;
v___y_2849_ = v___x_2980_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___x_2984_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v___y_2945_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2831_ = v___y_2946_;
v___y_2832_ = v___y_2947_;
v___y_2833_ = v___x_2982_;
v___y_2834_ = v___x_2981_;
v___y_2835_ = v___y_2948_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___y_2950_;
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2954_;
v___y_2842_ = v___y_2955_;
v___y_2843_ = v___x_2977_;
v___y_2844_ = v___y_2956_;
v___y_2845_ = v___y_2958_;
v___y_2846_ = v___y_2957_;
v___y_2847_ = v___y_2959_;
v___y_2848_ = v___x_2975_;
v___y_2849_ = v___x_2980_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___x_2985_;
goto v___jp_2830_;
}
}
}
v___jp_2986_:
{
lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3003_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2988_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = lean_array_get_size(v___y_2993_);
v___x_3006_ = lean_nat_dec_eq(v___x_3005_, v___x_2531_);
if (v___x_3006_ == 0)
{
if (lean_obj_tag(v___y_2989_) == 0)
{
v___y_2944_ = v___x_3006_;
v___y_2945_ = v___y_2987_;
v___y_2946_ = v___y_2990_;
v___y_2947_ = v___y_3001_;
v___y_2948_ = v___y_2992_;
v___y_2949_ = v_a_3004_;
v___y_2950_ = v___y_2998_;
v___y_2951_ = v___y_2999_;
v___y_2952_ = v___y_2993_;
v___y_2953_ = v___y_2995_;
v___y_2954_ = v___y_2997_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2991_;
v___y_2957_ = v_stxForExecution_2994_;
v___y_2958_ = v___y_2996_;
v___y_2959_ = v___y_3002_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___x_3006_;
goto v___jp_2943_;
}
else
{
v___y_2944_ = v___x_3006_;
v___y_2945_ = v___y_2987_;
v___y_2946_ = v___y_2990_;
v___y_2947_ = v___y_3001_;
v___y_2948_ = v___y_2992_;
v___y_2949_ = v_a_3004_;
v___y_2950_ = v___y_2998_;
v___y_2951_ = v___y_2999_;
v___y_2952_ = v___y_2993_;
v___y_2953_ = v___y_2995_;
v___y_2954_ = v___y_2997_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2991_;
v___y_2957_ = v_stxForExecution_2994_;
v___y_2958_ = v___y_2996_;
v___y_2959_ = v___y_3002_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_2991_;
goto v___jp_2943_;
}
}
else
{
lean_dec_ref(v___y_2993_);
if (lean_obj_tag(v___y_2989_) == 0)
{
uint8_t v___x_3007_; 
v___x_3007_ = 0;
v___y_2915_ = v___y_2987_;
v___y_2916_ = v___y_2990_;
v___y_2917_ = v___y_3001_;
v___y_2918_ = v___y_2992_;
v___y_2919_ = v_a_3004_;
v___y_2920_ = v___y_2998_;
v___y_2921_ = v___y_2999_;
v___y_2922_ = v___y_2995_;
v___y_2923_ = v___y_2997_;
v___y_2924_ = v___y_2989_;
v___y_2925_ = v___y_2991_;
v___y_2926_ = v___y_2996_;
v___y_2927_ = v_stxForExecution_2994_;
v___y_2928_ = v___y_3002_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___x_3007_;
goto v___jp_2914_;
}
else
{
if (v___y_2991_ == 0)
{
v___y_2915_ = v___y_2987_;
v___y_2916_ = v___y_2990_;
v___y_2917_ = v___y_3001_;
v___y_2918_ = v___y_2992_;
v___y_2919_ = v_a_3004_;
v___y_2920_ = v___y_2998_;
v___y_2921_ = v___y_2999_;
v___y_2922_ = v___y_2995_;
v___y_2923_ = v___y_2997_;
v___y_2924_ = v___y_2989_;
v___y_2925_ = v___y_2991_;
v___y_2926_ = v___y_2996_;
v___y_2927_ = v_stxForExecution_2994_;
v___y_2928_ = v___y_3002_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_2991_;
goto v___jp_2914_;
}
else
{
lean_object* v_ref_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_ref_3008_ = lean_ctor_get(v___y_3001_, 5);
v___x_3009_ = 0;
v___x_3010_ = l_Lean_SourceInfo_fromRef(v_ref_3008_, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3012_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3011_);
v___x_3013_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3017_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2987_) == 1)
{
lean_object* v_val_3018_; lean_object* v___x_3019_; 
v_val_3018_ = lean_ctor_get(v___y_2987_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v___y_2987_, 1);
v___x_3019_ = l_Array_mkArray1___redArg(v_val_3018_);
v___y_2886_ = v___y_2990_;
v___y_2887_ = v___y_3001_;
v___y_2888_ = v___y_2992_;
v___y_2889_ = v___x_3010_;
v___y_2890_ = v___x_3016_;
v___y_2891_ = v_a_3004_;
v___y_2892_ = v___y_2998_;
v___y_2893_ = v___y_2999_;
v___y_2894_ = v___y_2995_;
v___y_2895_ = v___x_3015_;
v___y_2896_ = v___x_3012_;
v___y_2897_ = v___y_2997_;
v___y_2898_ = v___y_2989_;
v___y_2899_ = v___y_2991_;
v___y_2900_ = v___x_3017_;
v___y_2901_ = v___y_2996_;
v___y_2902_ = v_stxForExecution_2994_;
v___y_2903_ = v___y_3002_;
v___y_2904_ = v___y_3000_;
v___y_2905_ = v___x_3019_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___y_2987_);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2886_ = v___y_2990_;
v___y_2887_ = v___y_3001_;
v___y_2888_ = v___y_2992_;
v___y_2889_ = v___x_3010_;
v___y_2890_ = v___x_3016_;
v___y_2891_ = v_a_3004_;
v___y_2892_ = v___y_2998_;
v___y_2893_ = v___y_2999_;
v___y_2894_ = v___y_2995_;
v___y_2895_ = v___x_3015_;
v___y_2896_ = v___x_3012_;
v___y_2897_ = v___y_2997_;
v___y_2898_ = v___y_2989_;
v___y_2899_ = v___y_2991_;
v___y_2900_ = v___x_3017_;
v___y_2901_ = v___y_2996_;
v___y_2902_ = v_stxForExecution_2994_;
v___y_2903_ = v___y_3002_;
v___y_2904_ = v___y_3000_;
v___y_2905_ = v___x_3020_;
goto v___jp_2885_;
}
}
}
}
}
v___jp_3021_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_inc_ref_n(v___y_3025_, 2);
v___x_3044_ = l_Array_append___redArg(v___y_3025_, v___y_3043_);
lean_dec_ref(v___y_3043_);
lean_inc_n(v___y_3040_, 2);
lean_inc_n(v___y_3029_, 2);
v___x_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___y_3029_);
lean_ctor_set(v___x_3045_, 1, v___y_3040_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3029_);
lean_ctor_set(v___x_3046_, 1, v___y_3040_);
lean_ctor_set(v___x_3046_, 2, v___y_3025_);
lean_inc(v___y_3033_);
v___x_3047_ = l_Lean_Syntax_node5(v___y_3029_, v___y_3030_, v___y_3042_, v___y_3033_, v___y_3023_, v___x_3045_, v___x_3046_);
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3033_;
v___y_2989_ = v___y_3034_;
v___y_2990_ = v___y_3024_;
v___y_2991_ = v___y_3035_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3031_;
v_stxForExecution_2994_ = v___x_3047_;
v___y_2995_ = v___y_3026_;
v___y_2996_ = v___y_3038_;
v___y_2997_ = v___y_3028_;
v___y_2998_ = v___y_3036_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3041_;
v___y_3001_ = v___y_3037_;
v___y_3002_ = v___y_3039_;
goto v___jp_2986_;
}
v___jp_3048_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_inc_ref(v___y_3051_);
v___x_3070_ = l_Array_append___redArg(v___y_3051_, v___y_3069_);
lean_dec_ref(v___y_3069_);
lean_inc(v___y_3067_);
lean_inc(v___y_3055_);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3055_);
lean_ctor_set(v___x_3071_, 1, v___y_3067_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
if (lean_obj_tag(v___y_3053_) == 1)
{
lean_object* v_val_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_val_3072_ = lean_ctor_get(v___y_3053_, 0);
v___x_3073_ = l_Lean_SourceInfo_fromRef(v_val_3072_, v___x_2516_);
v___x_3074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Array_mkArray1___redArg(v___x_3075_);
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___x_3071_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3062_;
v___y_3036_ = v___y_3061_;
v___y_3037_ = v___y_3064_;
v___y_3038_ = v___y_3063_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___x_3076_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___x_3071_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3062_;
v___y_3036_ = v___y_3061_;
v___y_3037_ = v___y_3064_;
v___y_3038_ = v___y_3063_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___x_3077_;
goto v___jp_3021_;
}
}
v___jp_3078_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_inc_ref_n(v___y_3091_, 2);
v___x_3101_ = l_Array_append___redArg(v___y_3091_, v___y_3100_);
lean_dec_ref(v___y_3100_);
lean_inc_n(v___y_3097_, 3);
lean_inc_n(v___y_3083_, 5);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3083_);
lean_ctor_set(v___x_3102_, 1, v___y_3097_);
lean_ctor_set(v___x_3102_, 2, v___x_3101_);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3083_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3106_ = l_Lean_Syntax_SepArray_ofElems(v___x_3105_, v___y_3087_);
v___x_3107_ = l_Array_append___redArg(v___y_3091_, v___x_3106_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___y_3083_);
lean_ctor_set(v___x_3108_, 1, v___y_3097_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3083_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node3(v___y_3083_, v___y_3097_, v___x_3104_, v___x_3108_, v___x_3110_);
lean_inc(v___y_3089_);
v___x_3112_ = l_Lean_Syntax_node5(v___y_3083_, v___y_3085_, v___y_3092_, v___y_3089_, v___y_3086_, v___x_3102_, v___x_3111_);
v___y_2987_ = v___y_3079_;
v___y_2988_ = v___y_3089_;
v___y_2989_ = v___y_3090_;
v___y_2990_ = v___y_3080_;
v___y_2991_ = v___y_3093_;
v___y_2992_ = v___y_3082_;
v___y_2993_ = v___y_3087_;
v_stxForExecution_2994_ = v___x_3112_;
v___y_2995_ = v___y_3081_;
v___y_2996_ = v___y_3096_;
v___y_2997_ = v___y_3084_;
v___y_2998_ = v___y_3094_;
v___y_2999_ = v___y_3088_;
v___y_3000_ = v___y_3099_;
v___y_3001_ = v___y_3095_;
v___y_3002_ = v___y_3098_;
goto v___jp_2986_;
}
v___jp_3113_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_inc_ref(v___y_3126_);
v___x_3135_ = l_Array_append___redArg(v___y_3126_, v___y_3134_);
lean_dec_ref(v___y_3134_);
lean_inc(v___y_3131_);
lean_inc(v___y_3117_);
v___x_3136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3117_);
lean_ctor_set(v___x_3136_, 1, v___y_3131_);
lean_ctor_set(v___x_3136_, 2, v___x_3135_);
if (lean_obj_tag(v___y_3118_) == 1)
{
lean_object* v_val_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_val_3137_ = lean_ctor_get(v___y_3118_, 0);
v___x_3138_ = l_Lean_SourceInfo_fromRef(v_val_3137_, v___x_2516_);
v___x_3139_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Array_mkArray1___redArg(v___x_3140_);
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3118_;
v___y_3083_ = v___y_3117_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___x_3136_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3122_;
v___y_3089_ = v___y_3123_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3126_;
v___y_3092_ = v___y_3125_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3129_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___x_3141_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3142_; 
v___x_3142_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3118_;
v___y_3083_ = v___y_3117_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___x_3136_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3122_;
v___y_3089_ = v___y_3123_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3126_;
v___y_3092_ = v___y_3125_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3129_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___x_3142_;
goto v___jp_3078_;
}
}
v___jp_3143_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_inc_ref_n(v___y_3147_, 2);
v___x_3166_ = l_Array_append___redArg(v___y_3147_, v___y_3165_);
lean_dec_ref(v___y_3165_);
lean_inc_n(v___y_3150_, 3);
lean_inc_n(v___y_3164_, 5);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3164_);
lean_ctor_set(v___x_3167_, 1, v___y_3150_);
lean_ctor_set(v___x_3167_, 2, v___x_3166_);
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3164_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3171_ = l_Lean_Syntax_SepArray_ofElems(v___x_3170_, v___y_3153_);
v___x_3172_ = l_Array_append___redArg(v___y_3147_, v___x_3171_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3164_);
lean_ctor_set(v___x_3173_, 1, v___y_3150_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___y_3164_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_Syntax_node3(v___y_3164_, v___y_3150_, v___x_3169_, v___x_3173_, v___x_3175_);
lean_inc(v___y_3155_);
v___x_3177_ = l_Lean_Syntax_node5(v___y_3164_, v___y_3151_, v___y_3161_, v___y_3155_, v___y_3146_, v___x_3167_, v___x_3176_);
v___y_2987_ = v___y_3144_;
v___y_2988_ = v___y_3155_;
v___y_2989_ = v___y_3156_;
v___y_2990_ = v___y_3145_;
v___y_2991_ = v___y_3157_;
v___y_2992_ = v___y_3149_;
v___y_2993_ = v___y_3153_;
v_stxForExecution_2994_ = v___x_3177_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3160_;
v___y_2997_ = v___y_3152_;
v___y_2998_ = v___y_3158_;
v___y_2999_ = v___y_3154_;
v___y_3000_ = v___y_3163_;
v___y_3001_ = v___y_3159_;
v___y_3002_ = v___y_3162_;
goto v___jp_2986_;
}
v___jp_3178_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_inc_ref(v___y_3181_);
v___x_3200_ = l_Array_append___redArg(v___y_3181_, v___y_3199_);
lean_dec_ref(v___y_3199_);
lean_inc(v___y_3183_);
lean_inc(v___y_3198_);
v___x_3201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3198_);
lean_ctor_set(v___x_3201_, 1, v___y_3183_);
lean_ctor_set(v___x_3201_, 2, v___x_3200_);
if (lean_obj_tag(v___y_3184_) == 1)
{
lean_object* v_val_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_val_3202_ = lean_ctor_get(v___y_3184_, 0);
v___x_3203_ = l_Lean_SourceInfo_fromRef(v_val_3202_, v___x_2516_);
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Array_mkArray1___redArg(v___x_3205_);
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___x_3201_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3183_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3187_;
v___y_3154_ = v___y_3188_;
v___y_3155_ = v___y_3189_;
v___y_3156_ = v___y_3190_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3191_;
v___y_3159_ = v___y_3194_;
v___y_3160_ = v___y_3193_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___y_3197_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___x_3206_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___x_3201_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3183_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3187_;
v___y_3154_ = v___y_3188_;
v___y_3155_ = v___y_3189_;
v___y_3156_ = v___y_3190_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3191_;
v___y_3159_ = v___y_3194_;
v___y_3160_ = v___y_3193_;
v___y_3161_ = v___y_3195_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___y_3197_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___x_3207_;
goto v___jp_3143_;
}
}
v___jp_3208_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_inc_ref_n(v___y_3220_, 2);
v___x_3231_ = l_Array_append___redArg(v___y_3220_, v___y_3230_);
lean_dec_ref(v___y_3230_);
lean_inc_n(v___y_3222_, 2);
lean_inc_n(v___y_3211_, 2);
v___x_3232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3232_, 0, v___y_3211_);
lean_ctor_set(v___x_3232_, 1, v___y_3222_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3233_, 0, v___y_3211_);
lean_ctor_set(v___x_3233_, 1, v___y_3222_);
lean_ctor_set(v___x_3233_, 2, v___y_3220_);
lean_inc(v___y_3218_);
v___x_3234_ = l_Lean_Syntax_node5(v___y_3211_, v___y_3224_, v___y_3228_, v___y_3218_, v___y_3215_, v___x_3232_, v___x_3233_);
v___y_2987_ = v___y_3209_;
v___y_2988_ = v___y_3218_;
v___y_2989_ = v___y_3219_;
v___y_2990_ = v___y_3210_;
v___y_2991_ = v___y_3221_;
v___y_2992_ = v___y_3213_;
v___y_2993_ = v___y_3216_;
v_stxForExecution_2994_ = v___x_3234_;
v___y_2995_ = v___y_3212_;
v___y_2996_ = v___y_3226_;
v___y_2997_ = v___y_3214_;
v___y_2998_ = v___y_3223_;
v___y_2999_ = v___y_3217_;
v___y_3000_ = v___y_3229_;
v___y_3001_ = v___y_3225_;
v___y_3002_ = v___y_3227_;
goto v___jp_2986_;
}
v___jp_3235_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_inc_ref(v___y_3246_);
v___x_3257_ = l_Array_append___redArg(v___y_3246_, v___y_3256_);
lean_dec_ref(v___y_3256_);
lean_inc(v___y_3249_);
lean_inc(v___y_3238_);
v___x_3258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3258_, 0, v___y_3238_);
lean_ctor_set(v___x_3258_, 1, v___y_3249_);
lean_ctor_set(v___x_3258_, 2, v___x_3257_);
if (lean_obj_tag(v___y_3240_) == 1)
{
lean_object* v_val_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_val_3259_ = lean_ctor_get(v___y_3240_, 0);
v___x_3260_ = l_Lean_SourceInfo_fromRef(v_val_3259_, v___x_2516_);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Array_mkArray1___redArg(v___x_3262_);
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___x_3258_;
v___y_3216_ = v___y_3242_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3247_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3251_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3253_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v___x_3263_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3264_; 
v___x_3264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___x_3258_;
v___y_3216_ = v___y_3242_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3247_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3251_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3253_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v___x_3264_;
goto v___jp_3208_;
}
}
v___jp_3265_:
{
lean_object* v_ref_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_ref_3282_ = lean_ctor_get(v___y_3278_, 5);
v___x_3283_ = l_Lean_SourceInfo_fromRef(v_ref_3282_, v___y_3281_);
v___x_3284_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3285_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3284_);
v___x_3286_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3287_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3290_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3266_) == 1)
{
lean_object* v_val_3291_; lean_object* v___x_3292_; 
v_val_3291_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3291_);
v___x_3292_ = l_Array_mkArray1___redArg(v_val_3291_);
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___y_3267_;
v___y_3051_ = v___x_3290_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___y_3269_;
v___y_3054_ = v___y_3270_;
v___y_3055_ = v___x_3283_;
v___y_3056_ = v___x_3285_;
v___y_3057_ = v___y_3271_;
v___y_3058_ = v___y_3272_;
v___y_3059_ = v___y_3273_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___y_3275_;
v___y_3062_ = v___y_3276_;
v___y_3063_ = v___y_3277_;
v___y_3064_ = v___y_3278_;
v___y_3065_ = v___y_3279_;
v___y_3066_ = v___y_3280_;
v___y_3067_ = v___x_3289_;
v___y_3068_ = v___x_3288_;
v___y_3069_ = v___x_3292_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___y_3267_;
v___y_3051_ = v___x_3290_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___y_3269_;
v___y_3054_ = v___y_3270_;
v___y_3055_ = v___x_3283_;
v___y_3056_ = v___x_3285_;
v___y_3057_ = v___y_3271_;
v___y_3058_ = v___y_3272_;
v___y_3059_ = v___y_3273_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___y_3275_;
v___y_3062_ = v___y_3276_;
v___y_3063_ = v___y_3277_;
v___y_3064_ = v___y_3278_;
v___y_3065_ = v___y_3279_;
v___y_3066_ = v___y_3280_;
v___y_3067_ = v___x_3289_;
v___y_3068_ = v___x_3288_;
v___y_3069_ = v___x_3293_;
goto v___jp_3048_;
}
}
v___jp_3294_:
{
if (v___y_3311_ == 0)
{
lean_object* v_ref_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_ref_3312_ = lean_ctor_get(v___y_3308_, 5);
v___x_3313_ = l_Lean_SourceInfo_fromRef(v_ref_3312_, v___y_3311_);
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3315_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3314_);
v___x_3316_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3320_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3295_) == 1)
{
lean_object* v_val_3321_; lean_object* v___x_3322_; 
v_val_3321_ = lean_ctor_get(v___y_3295_, 0);
lean_inc(v_val_3321_);
v___x_3322_ = l_Array_mkArray1___redArg(v_val_3321_);
v___y_3114_ = v___y_3295_;
v___y_3115_ = v___y_3296_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___x_3313_;
v___y_3118_ = v___y_3298_;
v___y_3119_ = v___y_3299_;
v___y_3120_ = v___x_3315_;
v___y_3121_ = v___y_3301_;
v___y_3122_ = v___y_3302_;
v___y_3123_ = v___y_3303_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___x_3318_;
v___y_3126_ = v___x_3320_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3306_;
v___y_3129_ = v___y_3307_;
v___y_3130_ = v___y_3308_;
v___y_3131_ = v___x_3319_;
v___y_3132_ = v___y_3309_;
v___y_3133_ = v___y_3310_;
v___y_3134_ = v___x_3322_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3114_ = v___y_3295_;
v___y_3115_ = v___y_3296_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___x_3313_;
v___y_3118_ = v___y_3298_;
v___y_3119_ = v___y_3299_;
v___y_3120_ = v___x_3315_;
v___y_3121_ = v___y_3301_;
v___y_3122_ = v___y_3302_;
v___y_3123_ = v___y_3303_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___x_3318_;
v___y_3126_ = v___x_3320_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3306_;
v___y_3129_ = v___y_3307_;
v___y_3130_ = v___y_3308_;
v___y_3131_ = v___x_3319_;
v___y_3132_ = v___y_3309_;
v___y_3133_ = v___y_3310_;
v___y_3134_ = v___x_3323_;
goto v___jp_3113_;
}
}
else
{
lean_object* v_ref_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_ref_3324_ = lean_ctor_get(v___y_3308_, 5);
v___x_3325_ = l_Lean_SourceInfo_fromRef(v_ref_3324_, v___y_3300_);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3327_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3326_);
v___x_3328_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3332_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3295_) == 1)
{
lean_object* v_val_3333_; lean_object* v___x_3334_; 
v_val_3333_ = lean_ctor_get(v___y_3295_, 0);
lean_inc(v_val_3333_);
v___x_3334_ = l_Array_mkArray1___redArg(v_val_3333_);
v___y_3179_ = v___y_3295_;
v___y_3180_ = v___y_3296_;
v___y_3181_ = v___x_3332_;
v___y_3182_ = v___y_3297_;
v___y_3183_ = v___x_3331_;
v___y_3184_ = v___y_3298_;
v___y_3185_ = v___x_3327_;
v___y_3186_ = v___y_3299_;
v___y_3187_ = v___y_3301_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___y_3304_;
v___y_3191_ = v___y_3305_;
v___y_3192_ = v___y_3306_;
v___y_3193_ = v___y_3307_;
v___y_3194_ = v___y_3308_;
v___y_3195_ = v___x_3330_;
v___y_3196_ = v___y_3309_;
v___y_3197_ = v___y_3310_;
v___y_3198_ = v___x_3325_;
v___y_3199_ = v___x_3334_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3179_ = v___y_3295_;
v___y_3180_ = v___y_3296_;
v___y_3181_ = v___x_3332_;
v___y_3182_ = v___y_3297_;
v___y_3183_ = v___x_3331_;
v___y_3184_ = v___y_3298_;
v___y_3185_ = v___x_3327_;
v___y_3186_ = v___y_3299_;
v___y_3187_ = v___y_3301_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___y_3304_;
v___y_3191_ = v___y_3305_;
v___y_3192_ = v___y_3306_;
v___y_3193_ = v___y_3307_;
v___y_3194_ = v___y_3308_;
v___y_3195_ = v___x_3330_;
v___y_3196_ = v___y_3309_;
v___y_3197_ = v___y_3310_;
v___y_3198_ = v___x_3325_;
v___y_3199_ = v___x_3335_;
goto v___jp_3178_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3352_ = lean_array_get_size(v_argsArray_3343_);
v___x_3353_ = lean_nat_dec_eq(v___x_3352_, v___x_2531_);
if (v___x_3353_ == 0)
{
if (lean_obj_tag(v___y_3339_) == 0)
{
v___y_3295_ = v___y_3338_;
v___y_3296_ = v___y_3340_;
v___y_3297_ = v___y_3344_;
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___y_3346_;
v___y_3300_ = v___x_3353_;
v___y_3301_ = v_argsArray_3343_;
v___y_3302_ = v___y_3348_;
v___y_3303_ = v___y_3337_;
v___y_3304_ = v___y_3339_;
v___y_3305_ = v___y_3347_;
v___y_3306_ = v___y_3341_;
v___y_3307_ = v___y_3345_;
v___y_3308_ = v___y_3350_;
v___y_3309_ = v___y_3351_;
v___y_3310_ = v___y_3349_;
v___y_3311_ = v___x_3353_;
goto v___jp_3294_;
}
else
{
v___y_3295_ = v___y_3338_;
v___y_3296_ = v___y_3340_;
v___y_3297_ = v___y_3344_;
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___y_3346_;
v___y_3300_ = v___x_3353_;
v___y_3301_ = v_argsArray_3343_;
v___y_3302_ = v___y_3348_;
v___y_3303_ = v___y_3337_;
v___y_3304_ = v___y_3339_;
v___y_3305_ = v___y_3347_;
v___y_3306_ = v___y_3341_;
v___y_3307_ = v___y_3345_;
v___y_3308_ = v___y_3350_;
v___y_3309_ = v___y_3351_;
v___y_3310_ = v___y_3349_;
v___y_3311_ = v___y_3341_;
goto v___jp_3294_;
}
}
else
{
if (lean_obj_tag(v___y_3339_) == 0)
{
uint8_t v___x_3354_; 
v___x_3354_ = 0;
v___y_3266_ = v___y_3338_;
v___y_3267_ = v___y_3340_;
v___y_3268_ = v___y_3344_;
v___y_3269_ = v___y_3342_;
v___y_3270_ = v___y_3346_;
v___y_3271_ = v_argsArray_3343_;
v___y_3272_ = v___y_3348_;
v___y_3273_ = v___y_3337_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___y_3347_;
v___y_3276_ = v___y_3341_;
v___y_3277_ = v___y_3345_;
v___y_3278_ = v___y_3350_;
v___y_3279_ = v___y_3351_;
v___y_3280_ = v___y_3349_;
v___y_3281_ = v___x_3354_;
goto v___jp_3265_;
}
else
{
if (v___y_3341_ == 0)
{
v___y_3266_ = v___y_3338_;
v___y_3267_ = v___y_3340_;
v___y_3268_ = v___y_3344_;
v___y_3269_ = v___y_3342_;
v___y_3270_ = v___y_3346_;
v___y_3271_ = v_argsArray_3343_;
v___y_3272_ = v___y_3348_;
v___y_3273_ = v___y_3337_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___y_3347_;
v___y_3276_ = v___y_3341_;
v___y_3277_ = v___y_3345_;
v___y_3278_ = v___y_3350_;
v___y_3279_ = v___y_3351_;
v___y_3280_ = v___y_3349_;
v___y_3281_ = v___y_3341_;
goto v___jp_3265_;
}
else
{
lean_object* v_ref_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_ref_3355_ = lean_ctor_get(v___y_3350_, 5);
v___x_3356_ = 0;
v___x_3357_ = l_Lean_SourceInfo_fromRef(v_ref_3355_, v___x_3356_);
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3359_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3358_);
v___x_3360_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3361_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3364_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3338_) == 1)
{
lean_object* v_val_3365_; lean_object* v___x_3366_; 
v_val_3365_ = lean_ctor_get(v___y_3338_, 0);
lean_inc(v_val_3365_);
v___x_3366_ = l_Array_mkArray1___redArg(v_val_3365_);
v___y_3236_ = v___y_3338_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___x_3357_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3342_;
v___y_3241_ = v___y_3346_;
v___y_3242_ = v_argsArray_3343_;
v___y_3243_ = v___y_3348_;
v___y_3244_ = v___y_3337_;
v___y_3245_ = v___y_3339_;
v___y_3246_ = v___x_3364_;
v___y_3247_ = v___y_3347_;
v___y_3248_ = v___y_3341_;
v___y_3249_ = v___x_3363_;
v___y_3250_ = v___x_3359_;
v___y_3251_ = v___y_3345_;
v___y_3252_ = v___y_3350_;
v___y_3253_ = v___x_3362_;
v___y_3254_ = v___y_3351_;
v___y_3255_ = v___y_3349_;
v___y_3256_ = v___x_3366_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3367_; 
v___x_3367_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3236_ = v___y_3338_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___x_3357_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3342_;
v___y_3241_ = v___y_3346_;
v___y_3242_ = v_argsArray_3343_;
v___y_3243_ = v___y_3348_;
v___y_3244_ = v___y_3337_;
v___y_3245_ = v___y_3339_;
v___y_3246_ = v___x_3364_;
v___y_3247_ = v___y_3347_;
v___y_3248_ = v___y_3341_;
v___y_3249_ = v___x_3363_;
v___y_3250_ = v___x_3359_;
v___y_3251_ = v___y_3345_;
v___y_3252_ = v___y_3350_;
v___y_3253_ = v___x_3362_;
v___y_3254_ = v___y_3351_;
v___y_3255_ = v___y_3349_;
v___y_3256_ = v___x_3367_;
goto v___jp_3235_;
}
}
}
}
}
v___jp_3368_:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3383_, v___y_3372_, v___y_3378_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v___x_3387_ = l_Lean_LibrarySuggestions_select(v_a_3386_, v___y_3384_, v___y_3372_, v___y_3378_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; size_t v_sz_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v_sz_3389_ = lean_array_size(v_a_3388_);
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3388_, v_sz_3389_, v___x_3390_, v___y_3374_, v___y_3380_, v___y_3383_, v___y_3375_, v___y_3371_, v___y_3372_, v___y_3378_, v___y_3381_, v___y_3382_);
lean_dec(v_a_3388_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___y_3337_ = v___y_3376_;
v___y_3338_ = v___y_3369_;
v___y_3339_ = v___y_3377_;
v___y_3340_ = v___y_3370_;
v___y_3341_ = v___y_3379_;
v___y_3342_ = v___y_3373_;
v_argsArray_3343_ = v_a_3392_;
v___y_3344_ = v___y_3380_;
v___y_3345_ = v___y_3383_;
v___y_3346_ = v___y_3375_;
v___y_3347_ = v___y_3371_;
v___y_3348_ = v___y_3372_;
v___y_3349_ = v___y_3378_;
v___y_3350_ = v___y_3381_;
v___y_3351_ = v___y_3382_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec(v___y_3373_);
lean_dec(v___y_3369_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3393_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3391_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3369_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3401_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3387_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3387_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3369_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3409_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3385_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3385_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
v___jp_3417_:
{
lean_object* v_config_3434_; uint8_t v_suggestions_3435_; 
v_config_3434_ = lean_ctor_get(v___y_3419_, 0);
lean_inc_ref(v_config_3434_);
lean_dec_ref(v___y_3419_);
v_suggestions_3435_ = lean_ctor_get_uint8(v_config_3434_, sizeof(void*)*3 + 26);
if (v_suggestions_3435_ == 0)
{
lean_dec_ref(v_config_3434_);
lean_dec_ref(v___f_2520_);
v___y_3337_ = v___y_3425_;
v___y_3338_ = v___y_3418_;
v___y_3339_ = v___y_3426_;
v___y_3340_ = v___y_3420_;
v___y_3341_ = v___y_3428_;
v___y_3342_ = v___y_3423_;
v_argsArray_3343_ = v___y_3433_;
v___y_3344_ = v___y_3429_;
v___y_3345_ = v___y_3432_;
v___y_3346_ = v___y_3424_;
v___y_3347_ = v___y_3421_;
v___y_3348_ = v___y_3422_;
v___y_3349_ = v___y_3427_;
v___y_3350_ = v___y_3430_;
v___y_3351_ = v___y_3431_;
goto v___jp_3336_;
}
else
{
lean_object* v_maxSuggestions_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_maxSuggestions_3436_ = lean_ctor_get(v_config_3434_, 2);
lean_inc(v_maxSuggestions_3436_);
lean_dec_ref(v_config_3434_);
v___x_3437_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3438_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3436_) == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = lean_unsigned_to_nat(100u);
v___x_3440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v___x_3437_);
lean_ctor_set(v___x_3440_, 2, v___f_2520_);
lean_ctor_set(v___x_3440_, 3, v___x_3438_);
v___y_3369_ = v___y_3418_;
v___y_3370_ = v___y_3420_;
v___y_3371_ = v___y_3421_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3433_;
v___y_3375_ = v___y_3424_;
v___y_3376_ = v___y_3425_;
v___y_3377_ = v___y_3426_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___y_3428_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3431_;
v___y_3383_ = v___y_3432_;
v___y_3384_ = v___x_3440_;
goto v___jp_3368_;
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3442_; 
v_val_3441_ = lean_ctor_get(v_maxSuggestions_3436_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v_maxSuggestions_3436_, 1);
v___x_3442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3442_, 0, v_val_3441_);
lean_ctor_set(v___x_3442_, 1, v___x_3437_);
lean_ctor_set(v___x_3442_, 2, v___f_2520_);
lean_ctor_set(v___x_3442_, 3, v___x_3438_);
v___y_3369_ = v___y_3418_;
v___y_3370_ = v___y_3420_;
v___y_3371_ = v___y_3421_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3433_;
v___y_3375_ = v___y_3424_;
v___y_3376_ = v___y_3425_;
v___y_3377_ = v___y_3426_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___y_3428_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3431_;
v___y_3383_ = v___y_3432_;
v___y_3384_ = v___x_3442_;
goto v___jp_3368_;
}
}
}
v___jp_3443_:
{
uint8_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = 1;
lean_inc(v___y_3448_);
v___x_3459_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3448_, v___x_3458_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3459_) == 0)
{
if (lean_obj_tag(v___y_3455_) == 1)
{
lean_object* v_a_3460_; lean_object* v_val_3461_; lean_object* v___x_3462_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_val_3461_ = lean_ctor_get(v___y_3455_, 0);
lean_inc(v_val_3461_);
lean_dec_ref_known(v___y_3455_, 1);
v___x_3462_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3461_);
lean_dec(v_val_3461_);
v___y_3418_ = v___y_3457_;
v___y_3419_ = v_a_3460_;
v___y_3420_ = v___x_3458_;
v___y_3421_ = v___y_3444_;
v___y_3422_ = v___y_3445_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3448_;
v___y_3426_ = v___y_3449_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___y_3451_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3453_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v___y_3456_;
v___y_3433_ = v___x_3462_;
goto v___jp_3417_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
lean_dec(v___y_3455_);
v_a_3463_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3464_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3418_ = v___y_3457_;
v___y_3419_ = v_a_3463_;
v___y_3420_ = v___x_3458_;
v___y_3421_ = v___y_3444_;
v___y_3422_ = v___y_3445_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3448_;
v___y_3426_ = v___y_3449_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___y_3451_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3453_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v___y_3456_;
v___y_3433_ = v___x_3464_;
goto v___jp_3417_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec(v___y_3446_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3465_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3459_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3459_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
v___jp_3473_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Syntax_getOptional_x3f(v___y_3478_);
lean_dec(v___y_3478_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_box(0);
v___y_3444_ = v___y_3483_;
v___y_3445_ = v___y_3484_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v___y_3482_;
v___y_3448_ = v___y_3474_;
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3485_;
v___y_3451_ = v___y_3476_;
v___y_3452_ = v___y_3480_;
v___y_3453_ = v___y_3486_;
v___y_3454_ = v___y_3487_;
v___y_3455_ = v_args_3479_;
v___y_3456_ = v___y_3481_;
v___y_3457_ = v___x_3489_;
goto v___jp_3443_;
}
else
{
lean_object* v_val_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_val_3490_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_val_3490_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_val_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
v___y_3444_ = v___y_3483_;
v___y_3445_ = v___y_3484_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v___y_3482_;
v___y_3448_ = v___y_3474_;
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3485_;
v___y_3451_ = v___y_3476_;
v___y_3452_ = v___y_3480_;
v___y_3453_ = v___y_3486_;
v___y_3454_ = v___y_3487_;
v___y_3455_ = v_args_3479_;
v___y_3456_ = v___y_3481_;
v___y_3457_ = v___x_3495_;
goto v___jp_3443_;
}
}
}
}
v___jp_3499_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3514_ = lean_unsigned_to_nat(3u);
v___x_3515_ = l_Lean_Syntax_getArg(v___y_3502_, v___x_3514_);
lean_dec(v___y_3502_);
v___x_3516_ = l_Lean_Syntax_isNone(v___x_3515_);
if (v___x_3516_ == 0)
{
uint8_t v___x_3517_; 
lean_inc(v___x_3515_);
v___x_3517_ = l_Lean_Syntax_matchesNull(v___x_3515_, v___x_3498_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_dec(v___x_3515_);
lean_dec(v_o_3505_);
lean_dec(v___y_3504_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3518_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3519_ = l_Lean_Syntax_getArg(v___x_3515_, v___x_2531_);
lean_dec(v___x_3515_);
v___x_3520_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3521_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3520_);
lean_inc(v___x_3519_);
v___x_3522_ = l_Lean_Syntax_isOfKind(v___x_3519_, v___x_3521_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3519_);
lean_dec(v_o_3505_);
lean_dec(v___y_3504_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v_args_3525_; lean_object* v___x_3526_; 
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3519_, v___x_3498_);
lean_dec(v___x_3519_);
v_args_3525_ = l_Lean_Syntax_getArgs(v___x_3524_);
lean_dec(v___x_3524_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_args_3525_);
v___y_3474_ = v___y_3500_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3503_;
v___y_3477_ = v_o_3505_;
v___y_3478_ = v___y_3504_;
v_args_3479_ = v___x_3526_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___y_3513_;
goto v___jp_3473_;
}
}
}
else
{
lean_object* v___x_3527_; 
lean_dec(v___x_3515_);
v___x_3527_ = lean_box(0);
v___y_3474_ = v___y_3500_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3503_;
v___y_3477_ = v_o_3505_;
v___y_3478_ = v___y_3504_;
v_args_3479_ = v___x_3527_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___y_3513_;
goto v___jp_3473_;
}
}
v___jp_3528_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3538_ = lean_unsigned_to_nat(2u);
v___x_3539_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_3538_);
v___x_3540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3541_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3540_);
lean_inc(v___x_3539_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v___x_3539_, v___x_3541_);
lean_dec(v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v___x_3539_);
lean_dec(v_bang_3529_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3543_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3543_;
}
else
{
lean_object* v_cfg_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_cfg_3544_ = l_Lean_Syntax_getArg(v___x_3539_, v___x_2531_);
v___x_3545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3546_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3545_);
lean_inc(v_cfg_3544_);
v___x_3547_ = l_Lean_Syntax_isOfKind(v_cfg_3544_, v___x_3546_);
lean_dec(v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_cfg_3544_);
lean_dec(v___x_3539_);
lean_dec(v_bang_3529_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3548_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3549_ = l_Lean_Syntax_getArg(v___x_3539_, v___x_3498_);
v___x_3550_ = l_Lean_Syntax_getArg(v___x_3539_, v___x_3538_);
v___x_3551_ = l_Lean_Syntax_isNone(v___x_3550_);
if (v___x_3551_ == 0)
{
uint8_t v___x_3552_; 
lean_inc(v___x_3550_);
v___x_3552_ = l_Lean_Syntax_matchesNull(v___x_3550_, v___x_3498_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
lean_dec(v___x_3550_);
lean_dec(v___x_3549_);
lean_dec(v_cfg_3544_);
lean_dec(v___x_3539_);
lean_dec(v_bang_3529_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3553_;
}
else
{
lean_object* v_o_3554_; lean_object* v___x_3555_; 
v_o_3554_ = l_Lean_Syntax_getArg(v___x_3550_, v___x_2531_);
lean_dec(v___x_3550_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_o_3554_);
v___y_3500_ = v_cfg_3544_;
v___y_3501_ = v_bang_3529_;
v___y_3502_ = v___x_3539_;
v___y_3503_ = v___x_3547_;
v___y_3504_ = v___x_3549_;
v_o_3505_ = v___x_3555_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
v___y_3511_ = v___y_3535_;
v___y_3512_ = v___y_3536_;
v___y_3513_ = v___y_3537_;
goto v___jp_3499_;
}
}
else
{
lean_object* v___x_3556_; 
lean_dec(v___x_3550_);
v___x_3556_ = lean_box(0);
v___y_3500_ = v_cfg_3544_;
v___y_3501_ = v_bang_3529_;
v___y_3502_ = v___x_3539_;
v___y_3503_ = v___x_3547_;
v___y_3504_ = v___x_3549_;
v_o_3505_ = v___x_3556_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
v___y_3511_ = v___y_3535_;
v___y_3512_ = v___y_3536_;
v___y_3513_ = v___y_3537_;
goto v___jp_3499_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3564_, lean_object* v_stx_3565_, lean_object* v___x_3566_, lean_object* v___x_3567_, lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v___f_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v___x_39049__boxed_3580_; uint8_t v___x_39050__boxed_3581_; lean_object* v_res_3582_; 
v___x_39049__boxed_3580_ = lean_unbox(v___x_3564_);
v___x_39050__boxed_3581_ = lean_unbox(v___x_3566_);
v_res_3582_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39049__boxed_3580_, v_stx_3565_, v___x_39050__boxed_3581_, v___x_3567_, v___x_3568_, v___x_3569_, v___f_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v_stx_3565_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; uint8_t v___x_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___y_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3602_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3589_);
v___x_3603_ = l_Lean_Syntax_isOfKind(v_stx_3589_, v___x_3602_);
v___x_3604_ = 1;
v___f_3605_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3606_ = lean_box(v___x_3603_);
v___x_3607_ = lean_box(v___x_3604_);
v___y_3608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3608_, 0, v___x_3606_);
lean_closure_set(v___y_3608_, 1, v_stx_3589_);
lean_closure_set(v___y_3608_, 2, v___x_3607_);
lean_closure_set(v___y_3608_, 3, v___x_3599_);
lean_closure_set(v___y_3608_, 4, v___x_3600_);
lean_closure_set(v___y_3608_, 5, v___x_3601_);
lean_closure_set(v___y_3608_, 6, v___f_3605_);
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3609_, 0, v___y_3608_);
v___x_3610_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3609_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3622_, lean_object* v_as_3623_, lean_object* v_as_x27_3624_, lean_object* v_b_3625_, lean_object* v_a_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3622_, v_as_x27_3624_, v_b_3625_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3637_, lean_object* v_as_3638_, lean_object* v_as_x27_3639_, lean_object* v_b_3640_, lean_object* v_a_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3637_, v_as_3638_, v_as_x27_3639_, v_b_3640_, v_a_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v_as_x27_3639_);
lean_dec(v_as_3638_);
lean_dec(v___x_3637_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3659_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3662_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3663_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3659_, v___x_3660_, v___x_3661_, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3693_ = l_Lean_addBuiltinDeclarationRanges(v___x_3691_, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3696_, lean_object* v_simprocs_3697_, lean_object* v_fvarIdsToSimp_3698_, uint8_t v_simplifyTarget_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = lean_unsigned_to_nat(32u);
v___x_3709_ = lean_mk_empty_array_with_capacity(v___x_3708_);
lean_dec_ref(v___x_3709_);
v___x_3710_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3711_ = l_Lean_Meta_dsimpGoal(v_a_3707_, v_ctx_3696_, v_simprocs_3697_, v_simplifyTarget_3699_, v_fvarIdsToSimp_3698_, v___x_3710_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v_fst_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v_fst_3713_ = lean_ctor_get(v_a_3712_, 0);
if (lean_obj_tag(v_fst_3713_) == 0)
{
lean_object* v_snd_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_snd_3714_ = lean_ctor_get(v_a_3712_, 1);
lean_inc(v_snd_3714_);
lean_dec(v_a_3712_);
v___x_3715_ = lean_box(0);
v___x_3716_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3715_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3723_ == 0)
{
lean_object* v_unused_3724_; 
v_unused_3724_ = lean_ctor_get(v___x_3716_, 0);
lean_dec(v_unused_3724_);
v___x_3718_ = v___x_3716_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_dec(v___x_3716_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v_snd_3714_);
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_snd_3714_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_snd_3714_);
v_a_3725_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3716_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3716_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_snd_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3759_; 
lean_inc_ref(v_fst_3713_);
v_snd_3733_ = lean_ctor_get(v_a_3712_, 1);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3712_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v_a_3712_, 0);
lean_dec(v_unused_3760_);
v___x_3735_ = v_a_3712_;
v_isShared_3736_ = v_isSharedCheck_3759_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_snd_3733_);
lean_dec(v_a_3712_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3759_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v_val_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v_val_3737_ = lean_ctor_get(v_fst_3713_, 0);
lean_inc(v_val_3737_);
lean_dec_ref_known(v_fst_3713_, 1);
v___x_3738_ = lean_box(0);
if (v_isShared_3736_ == 0)
{
lean_ctor_set_tag(v___x_3735_, 1);
lean_ctor_set(v___x_3735_, 1, v___x_3738_);
lean_ctor_set(v___x_3735_, 0, v_val_3737_);
v___x_3740_ = v___x_3735_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_val_3737_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3740_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3749_);
v___x_3743_ = v___x_3741_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v_snd_3733_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_snd_3733_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_snd_3733_);
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_a_3761_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3711_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3711_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v_fvarIdsToSimp_3698_);
lean_dec_ref(v_simprocs_3697_);
lean_dec_ref(v_ctx_3696_);
v_a_3769_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3706_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3706_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3777_, lean_object* v_simprocs_3778_, lean_object* v_fvarIdsToSimp_3779_, lean_object* v_simplifyTarget_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
uint8_t v_simplifyTarget_boxed_3787_; lean_object* v_res_3788_; 
v_simplifyTarget_boxed_3787_ = lean_unbox(v_simplifyTarget_3780_);
v_res_3788_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3777_, v_simprocs_3778_, v_fvarIdsToSimp_3779_, v_simplifyTarget_boxed_3787_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3789_, lean_object* v_simprocs_3790_, lean_object* v_fvarIdsToSimp_3791_, uint8_t v_simplifyTarget_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3789_, v_simprocs_3790_, v_fvarIdsToSimp_3791_, v_simplifyTarget_3792_, v_a_3794_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3803_, lean_object* v_simprocs_3804_, lean_object* v_fvarIdsToSimp_3805_, lean_object* v_simplifyTarget_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
uint8_t v_simplifyTarget_boxed_3816_; lean_object* v_res_3817_; 
v_simplifyTarget_boxed_3816_ = lean_unbox(v_simplifyTarget_3806_);
v_res_3817_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3803_, v_simprocs_3804_, v_fvarIdsToSimp_3805_, v_simplifyTarget_boxed_3816_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3818_, lean_object* v_simprocs_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3821_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3829_, 1);
v___x_3831_ = l_Lean_MVarId_getNondepPropHyps(v_a_3830_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = 1;
v___x_3834_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3818_, v_simprocs_3819_, v_a_3832_, v___x_3833_, v___y_3821_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3834_;
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_simprocs_3819_);
lean_dec_ref(v_ctx_3818_);
v_a_3835_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3831_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3831_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v_simprocs_3819_);
lean_dec_ref(v_ctx_3818_);
v_a_3843_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3829_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3829_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3851_, lean_object* v_simprocs_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3851_, v_simprocs_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3863_, lean_object* v_ctx_3864_, lean_object* v_simprocs_3865_, uint8_t v_type_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3863_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3864_, v_simprocs_3865_, v_a_3877_, v_type_3866_, v___y_3868_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3878_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_simprocs_3865_);
lean_dec_ref(v_ctx_3864_);
v_a_3879_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3876_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3876_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3887_, lean_object* v_ctx_3888_, lean_object* v_simprocs_3889_, lean_object* v_type_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
uint8_t v_type_633__boxed_3900_; lean_object* v_res_3901_; 
v_type_633__boxed_3900_ = lean_unbox(v_type_3890_);
v_res_3901_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3887_, v_ctx_3888_, v_simprocs_3889_, v_type_633__boxed_3900_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3902_, lean_object* v_simprocs_3903_, lean_object* v_loc_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
if (lean_obj_tag(v_loc_3904_) == 0)
{
lean_object* v___f_3914_; lean_object* v___x_3915_; 
v___f_3914_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3914_, 0, v_ctx_3902_);
lean_closure_set(v___f_3914_, 1, v_simprocs_3903_);
v___x_3915_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3914_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
return v___x_3915_;
}
else
{
lean_object* v_hypotheses_3916_; uint8_t v_type_3917_; lean_object* v___x_3918_; lean_object* v___f_3919_; lean_object* v___x_3920_; 
v_hypotheses_3916_ = lean_ctor_get(v_loc_3904_, 0);
lean_inc_ref(v_hypotheses_3916_);
v_type_3917_ = lean_ctor_get_uint8(v_loc_3904_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3904_, 1);
v___x_3918_ = lean_box(v_type_3917_);
v___f_3919_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3919_, 0, v_hypotheses_3916_);
lean_closure_set(v___f_3919_, 1, v_ctx_3902_);
lean_closure_set(v___f_3919_, 2, v_simprocs_3903_);
lean_closure_set(v___f_3919_, 3, v___x_3918_);
v___x_3920_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3919_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
return v___x_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3921_, lean_object* v_simprocs_3922_, lean_object* v_loc_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3921_, v_simprocs_3922_, v_loc_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3938_, lean_object* v_stx_3939_, uint8_t v___x_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v___x_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
if (v___x_3938_ == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_3953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; lean_object* v_tk_3955_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v_stx_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; uint8_t v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; uint8_t v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; uint8_t v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; uint8_t v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; uint8_t v___y_4260_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; uint8_t v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4310_; uint8_t v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v_args_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___x_4336_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v_o_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v_bang_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_3954_ = lean_unsigned_to_nat(0u);
v_tk_3955_ = l_Lean_Syntax_getArg(v_stx_3939_, v___x_3954_);
v___x_4336_ = lean_unsigned_to_nat(1u);
v___x_4393_ = l_Lean_Syntax_getArg(v_stx_3939_, v___x_4336_);
v___x_4394_ = l_Lean_Syntax_isNone(v___x_4393_);
if (v___x_4394_ == 0)
{
uint8_t v___x_4395_; 
lean_inc(v___x_4393_);
v___x_4395_ = l_Lean_Syntax_matchesNull(v___x_4393_, v___x_4336_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_dec(v___x_4393_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4396_;
}
else
{
lean_object* v_bang_4397_; lean_object* v___x_4398_; 
v_bang_4397_ = l_Lean_Syntax_getArg(v___x_4393_, v___x_3954_);
lean_dec(v___x_4393_);
v___x_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_bang_4397_);
v_bang_4366_ = v___x_4398_;
v___y_4367_ = v___y_3944_;
v___y_4368_ = v___y_3945_;
v___y_4369_ = v___y_3946_;
v___y_4370_ = v___y_3947_;
v___y_4371_ = v___y_3948_;
v___y_4372_ = v___y_3949_;
v___y_4373_ = v___y_3950_;
v___y_4374_ = v___y_3951_;
goto v___jp_4365_;
}
}
else
{
lean_object* v___x_4399_; 
lean_dec(v___x_4393_);
v___x_4399_ = lean_box(0);
v_bang_4366_ = v___x_4399_;
v___y_4367_ = v___y_3944_;
v___y_4368_ = v___y_3945_;
v___y_4369_ = v___y_3946_;
v___y_4370_ = v___y_3947_;
v___y_4371_ = v___y_3948_;
v___y_4372_ = v___y_3949_;
v___y_4373_ = v___y_3950_;
v___y_4374_ = v___y_3951_;
goto v___jp_4365_;
}
v___jp_3956_:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3965_, v___y_3958_, v___y_3968_, v___y_3966_, v___y_3967_, v___y_3962_, v___y_3957_, v___y_3964_, v___y_3961_, v___y_3963_, v___y_3959_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v_usedTheorems_3971_; lean_object* v_diag_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4014_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v_usedTheorems_3971_ = lean_ctor_get(v_a_3970_, 0);
v_diag_3972_ = lean_ctor_get(v_a_3970_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3974_ = v_a_3970_;
v_isShared_3975_ = v_isSharedCheck_4014_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_diag_3972_);
lean_inc(v_usedTheorems_3971_);
lean_dec(v_a_3970_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4014_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3960_, v_usedTheorems_3971_, v___y_3964_, v___y_3961_, v___y_3963_, v___y_3959_);
lean_dec_ref(v_usedTheorems_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v_ref_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v_ref_3978_ = lean_ctor_get(v___y_3963_, 5);
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v_a_3977_);
lean_ctor_set(v___x_3974_, 0, v___x_3979_);
v___x_3981_ = v___x_3974_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_3977_);
v___x_3981_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3982_ = lean_box(0);
v___x_3983_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
lean_ctor_set(v___x_3983_, 3, v___x_3982_);
lean_ctor_set(v___x_3983_, 4, v___x_3982_);
lean_ctor_set(v___x_3983_, 5, v___x_3982_);
lean_inc(v_ref_3978_);
v___x_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_ref_3978_);
v___x_3985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3986_ = 4;
v___x_3987_ = l_Lean_MessageData_nil;
v___x_3988_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3955_, v___x_3983_, v___x_3984_, v___x_3985_, v___x_3982_, v___x_3986_, v___x_3987_, v___y_3963_, v___y_3959_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v___x_3988_, 0);
lean_dec(v_unused_3996_);
v___x_3990_ = v___x_3988_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v_diag_3972_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_diag_3972_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec_ref(v_diag_3972_);
v_a_3997_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3988_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3988_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_del_object(v___x_3974_);
lean_dec_ref(v_diag_3972_);
lean_dec(v_tk_3955_);
v_a_4006_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3976_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3976_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v___y_3960_);
lean_dec(v_tk_3955_);
v_a_4015_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3969_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3969_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
v___jp_4023_:
{
if (lean_obj_tag(v___y_4027_) == 0)
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4037_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
lean_ctor_set_uint8(v___x_4037_, sizeof(void*)*1, v___x_3940_);
v___y_3957_ = v___y_4024_;
v___y_3958_ = v___y_4025_;
v___y_3959_ = v___y_4026_;
v___y_3960_ = v___y_4030_;
v___y_3961_ = v___y_4029_;
v___y_3962_ = v___y_4028_;
v___y_3963_ = v___y_4031_;
v___y_3964_ = v___y_4032_;
v___y_3965_ = v___y_4035_;
v___y_3966_ = v___y_4033_;
v___y_3967_ = v___y_4034_;
v___y_3968_ = v___x_4037_;
goto v___jp_3956_;
}
else
{
lean_object* v_val_4038_; lean_object* v___x_4039_; 
v_val_4038_ = lean_ctor_get(v___y_4027_, 0);
lean_inc(v_val_4038_);
lean_dec_ref_known(v___y_4027_, 1);
v___x_4039_ = l_Lean_Elab_Tactic_expandLocation(v_val_4038_);
lean_dec(v_val_4038_);
v___y_3957_ = v___y_4024_;
v___y_3958_ = v___y_4025_;
v___y_3959_ = v___y_4026_;
v___y_3960_ = v___y_4030_;
v___y_3961_ = v___y_4029_;
v___y_3962_ = v___y_4028_;
v___y_3963_ = v___y_4031_;
v___y_3964_ = v___y_4032_;
v___y_3965_ = v___y_4035_;
v___y_3966_ = v___y_4033_;
v___y_3967_ = v___y_4034_;
v___y_3968_ = v___x_4039_;
goto v___jp_3956_;
}
}
v___jp_4040_:
{
uint8_t v___x_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4053_ = 0;
v___x_4054_ = 2;
v___x_4055_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4056_ = lean_box(v___x_4053_);
v___x_4057_ = lean_box(v___x_4054_);
v___x_4058_ = lean_box(v___x_4053_);
lean_inc(v_stx_4044_);
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4059_, 0, v_stx_4044_);
lean_closure_set(v___x_4059_, 1, v___x_4056_);
lean_closure_set(v___x_4059_, 2, v___x_4057_);
lean_closure_set(v___x_4059_, 3, v___x_4058_);
lean_closure_set(v___x_4059_, 4, v___x_4055_);
v___x_4060_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4059_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
if (lean_obj_tag(v___y_4041_) == 0)
{
lean_object* v_ctx_4062_; lean_object* v_simprocs_4063_; 
v_ctx_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc_ref(v_ctx_4062_);
v_simprocs_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc_ref(v_simprocs_4063_);
lean_dec(v_a_4061_);
v___y_4024_ = v___y_4048_;
v___y_4025_ = v_simprocs_4063_;
v___y_4026_ = v___y_4052_;
v___y_4027_ = v___y_4042_;
v___y_4028_ = v___y_4047_;
v___y_4029_ = v___y_4050_;
v___y_4030_ = v_stx_4044_;
v___y_4031_ = v___y_4051_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v___y_4045_;
v___y_4034_ = v___y_4046_;
v___y_4035_ = v_ctx_4062_;
goto v___jp_4023_;
}
else
{
lean_dec_ref_known(v___y_4041_, 1);
if (v___y_4043_ == 0)
{
lean_object* v_ctx_4064_; lean_object* v_simprocs_4065_; 
v_ctx_4064_ = lean_ctor_get(v_a_4061_, 0);
lean_inc_ref(v_ctx_4064_);
v_simprocs_4065_ = lean_ctor_get(v_a_4061_, 1);
lean_inc_ref(v_simprocs_4065_);
lean_dec(v_a_4061_);
v___y_4024_ = v___y_4048_;
v___y_4025_ = v_simprocs_4065_;
v___y_4026_ = v___y_4052_;
v___y_4027_ = v___y_4042_;
v___y_4028_ = v___y_4047_;
v___y_4029_ = v___y_4050_;
v___y_4030_ = v_stx_4044_;
v___y_4031_ = v___y_4051_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v___y_4045_;
v___y_4034_ = v___y_4046_;
v___y_4035_ = v_ctx_4064_;
goto v___jp_4023_;
}
else
{
lean_object* v_ctx_4066_; lean_object* v_simprocs_4067_; lean_object* v___x_4068_; 
v_ctx_4066_ = lean_ctor_get(v_a_4061_, 0);
lean_inc_ref(v_ctx_4066_);
v_simprocs_4067_ = lean_ctor_get(v_a_4061_, 1);
lean_inc_ref(v_simprocs_4067_);
lean_dec(v_a_4061_);
v___x_4068_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4066_);
v___y_4024_ = v___y_4048_;
v___y_4025_ = v_simprocs_4067_;
v___y_4026_ = v___y_4052_;
v___y_4027_ = v___y_4042_;
v___y_4028_ = v___y_4047_;
v___y_4029_ = v___y_4050_;
v___y_4030_ = v_stx_4044_;
v___y_4031_ = v___y_4051_;
v___y_4032_ = v___y_4049_;
v___y_4033_ = v___y_4045_;
v___y_4034_ = v___y_4046_;
v___y_4035_ = v___x_4068_;
goto v___jp_4023_;
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_stx_4044_);
lean_dec(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec(v_tk_3955_);
v_a_4069_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4060_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4060_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
v___jp_4077_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_inc_ref(v___y_4096_);
v___x_4099_ = l_Array_append___redArg(v___y_4096_, v___y_4098_);
lean_dec_ref(v___y_4098_);
lean_inc(v___y_4082_);
lean_inc(v___y_4095_);
v___x_4100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4100_, 0, v___y_4095_);
lean_ctor_set(v___x_4100_, 1, v___y_4082_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
v___x_4101_ = l_Lean_Syntax_node6(v___y_4095_, v___y_4084_, v___y_4093_, v___y_4097_, v___y_4092_, v___y_4085_, v___y_4086_, v___x_4100_);
v___y_4041_ = v___y_4083_;
v___y_4042_ = v___y_4094_;
v___y_4043_ = v___y_4087_;
v_stx_4044_ = v___x_4101_;
v___y_4045_ = v___y_4079_;
v___y_4046_ = v___y_4080_;
v___y_4047_ = v___y_4090_;
v___y_4048_ = v___y_4081_;
v___y_4049_ = v___y_4088_;
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4091_;
v___y_4052_ = v___y_4078_;
goto v___jp_4040_;
}
v___jp_4102_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_inc_ref(v___y_4120_);
v___x_4123_ = l_Array_append___redArg(v___y_4120_, v___y_4122_);
lean_dec_ref(v___y_4122_);
lean_inc(v___y_4107_);
lean_inc(v___y_4119_);
v___x_4124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4124_, 0, v___y_4119_);
lean_ctor_set(v___x_4124_, 1, v___y_4107_);
lean_ctor_set(v___x_4124_, 2, v___x_4123_);
if (lean_obj_tag(v___y_4118_) == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4106_;
v___y_4082_ = v___y_4107_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___x_4124_;
v___y_4087_ = v___y_4111_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4115_;
v___y_4093_ = v___y_4117_;
v___y_4094_ = v___y_4118_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___y_4121_;
v___y_4098_ = v___x_4125_;
goto v___jp_4077_;
}
else
{
lean_object* v_val_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_val_4126_ = lean_ctor_get(v___y_4118_, 0);
v___x_4127_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4126_);
v___x_4128_ = lean_array_push(v___x_4127_, v_val_4126_);
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4106_;
v___y_4082_ = v___y_4107_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___x_4124_;
v___y_4087_ = v___y_4111_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4115_;
v___y_4093_ = v___y_4117_;
v___y_4094_ = v___y_4118_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___y_4121_;
v___y_4098_ = v___x_4128_;
goto v___jp_4077_;
}
}
v___jp_4129_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_inc_ref(v___y_4147_);
v___x_4150_ = l_Array_append___redArg(v___y_4147_, v___y_4149_);
lean_dec_ref(v___y_4149_);
lean_inc(v___y_4134_);
lean_inc(v___y_4146_);
v___x_4151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4151_, 0, v___y_4146_);
lean_ctor_set(v___x_4151_, 1, v___y_4134_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
if (lean_obj_tag(v___y_4137_) == 1)
{
lean_object* v_val_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_val_4152_ = lean_ctor_get(v___y_4137_, 0);
lean_inc(v_val_4152_);
lean_dec_ref_known(v___y_4137_, 1);
v___x_4153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4146_, 3);
v___x_4154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___y_4146_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
lean_inc_ref(v___y_4147_);
v___x_4155_ = l_Array_append___redArg(v___y_4147_, v_val_4152_);
lean_dec(v_val_4152_);
lean_inc(v___y_4134_);
v___x_4156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4146_);
lean_ctor_set(v___x_4156_, 1, v___y_4134_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
v___x_4157_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___y_4146_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Array_mkArray3___redArg(v___x_4154_, v___x_4156_, v___x_4158_);
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___y_4133_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___x_4151_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4144_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4148_;
v___y_4122_ = v___x_4159_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4160_; 
lean_dec(v___y_4137_);
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___y_4133_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___x_4151_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4144_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4148_;
v___y_4122_ = v___x_4160_;
goto v___jp_4102_;
}
}
v___jp_4161_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_inc_ref(v___y_4179_);
v___x_4183_ = l_Array_append___redArg(v___y_4179_, v___y_4182_);
lean_dec_ref(v___y_4182_);
lean_inc(v___y_4172_);
lean_inc(v___y_4168_);
v___x_4184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4184_, 0, v___y_4168_);
lean_ctor_set(v___x_4184_, 1, v___y_4172_);
lean_ctor_set(v___x_4184_, 2, v___x_4183_);
v___x_4185_ = l_Lean_Syntax_node6(v___y_4168_, v___y_4180_, v___y_4176_, v___y_4181_, v___y_4177_, v___y_4167_, v___y_4170_, v___x_4184_);
v___y_4041_ = v___y_4166_;
v___y_4042_ = v___y_4178_;
v___y_4043_ = v___y_4169_;
v_stx_4044_ = v___x_4185_;
v___y_4045_ = v___y_4163_;
v___y_4046_ = v___y_4164_;
v___y_4047_ = v___y_4174_;
v___y_4048_ = v___y_4165_;
v___y_4049_ = v___y_4171_;
v___y_4050_ = v___y_4173_;
v___y_4051_ = v___y_4175_;
v___y_4052_ = v___y_4162_;
goto v___jp_4040_;
}
v___jp_4186_:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_inc_ref(v___y_4203_);
v___x_4207_ = l_Array_append___redArg(v___y_4203_, v___y_4206_);
lean_dec_ref(v___y_4206_);
lean_inc(v___y_4195_);
lean_inc(v___y_4193_);
v___x_4208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4208_, 0, v___y_4193_);
lean_ctor_set(v___x_4208_, 1, v___y_4195_);
lean_ctor_set(v___x_4208_, 2, v___x_4207_);
if (lean_obj_tag(v___y_4202_) == 0)
{
lean_object* v___x_4209_; 
v___x_4209_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___y_4190_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___x_4208_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4195_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4197_;
v___y_4175_ = v___y_4199_;
v___y_4176_ = v___y_4200_;
v___y_4177_ = v___y_4201_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___x_4209_;
goto v___jp_4161_;
}
else
{
lean_object* v_val_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_val_4210_ = lean_ctor_get(v___y_4202_, 0);
v___x_4211_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4210_);
v___x_4212_ = lean_array_push(v___x_4211_, v_val_4210_);
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___y_4190_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___x_4208_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4195_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4197_;
v___y_4175_ = v___y_4199_;
v___y_4176_ = v___y_4200_;
v___y_4177_ = v___y_4201_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4204_;
v___y_4181_ = v___y_4205_;
v___y_4182_ = v___x_4212_;
goto v___jp_4161_;
}
}
v___jp_4213_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_inc_ref(v___y_4230_);
v___x_4234_ = l_Array_append___redArg(v___y_4230_, v___y_4233_);
lean_dec_ref(v___y_4233_);
lean_inc(v___y_4222_);
lean_inc(v___y_4219_);
v___x_4235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4235_, 0, v___y_4219_);
lean_ctor_set(v___x_4235_, 1, v___y_4222_);
lean_ctor_set(v___x_4235_, 2, v___x_4234_);
if (lean_obj_tag(v___y_4220_) == 1)
{
lean_object* v_val_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v_val_4236_ = lean_ctor_get(v___y_4220_, 0);
lean_inc(v_val_4236_);
lean_dec_ref_known(v___y_4220_, 1);
v___x_4237_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4219_, 3);
v___x_4238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___y_4219_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
lean_inc_ref(v___y_4230_);
v___x_4239_ = l_Array_append___redArg(v___y_4230_, v_val_4236_);
lean_dec(v_val_4236_);
lean_inc(v___y_4222_);
v___x_4240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4240_, 0, v___y_4219_);
lean_ctor_set(v___x_4240_, 1, v___y_4222_);
lean_ctor_set(v___x_4240_, 2, v___x_4239_);
v___x_4241_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___y_4219_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = l_Array_mkArray3___redArg(v___x_4238_, v___x_4240_, v___x_4242_);
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___y_4216_;
v___y_4190_ = v___y_4217_;
v___y_4191_ = v___y_4218_;
v___y_4192_ = v___x_4235_;
v___y_4193_ = v___y_4219_;
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4224_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___x_4243_;
goto v___jp_4186_;
}
else
{
lean_object* v___x_4244_; 
lean_dec(v___y_4220_);
v___x_4244_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___y_4216_;
v___y_4190_ = v___y_4217_;
v___y_4191_ = v___y_4218_;
v___y_4192_ = v___x_4235_;
v___y_4193_ = v___y_4219_;
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4224_;
v___y_4198_ = v___y_4225_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4227_;
v___y_4201_ = v___y_4228_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4231_;
v___y_4205_ = v___y_4232_;
v___y_4206_ = v___x_4244_;
goto v___jp_4186_;
}
}
v___jp_4245_:
{
lean_object* v_ref_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_ref_4261_ = lean_ctor_get(v___y_4256_, 5);
v___x_4262_ = l_Lean_SourceInfo_fromRef(v_ref_4261_, v___y_4260_);
v___x_4263_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4264_ = l_Lean_Name_mkStr4(v___x_3941_, v___x_3942_, v___x_3943_, v___x_4263_);
v___x_4265_ = l_Lean_SourceInfo_fromRef(v_tk_3955_, v___x_3940_);
v___x_4266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
lean_ctor_set(v___x_4266_, 1, v___x_4263_);
v___x_4267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4268_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4262_);
v___x_4269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4262_);
lean_ctor_set(v___x_4269_, 1, v___x_4267_);
lean_ctor_set(v___x_4269_, 2, v___x_4268_);
if (lean_obj_tag(v___y_4258_) == 1)
{
lean_object* v_val_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_val_4270_ = lean_ctor_get(v___y_4258_, 0);
lean_inc(v_val_4270_);
lean_dec_ref_known(v___y_4258_, 1);
v___x_4271_ = l_Lean_SourceInfo_fromRef(v_val_4270_, v___x_3940_);
lean_dec(v_val_4270_);
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Array_mkArray1___redArg(v___x_4273_);
v___y_4130_ = v___y_4246_;
v___y_4131_ = v___y_4247_;
v___y_4132_ = v___y_4248_;
v___y_4133_ = v___y_4249_;
v___y_4134_ = v___x_4267_;
v___y_4135_ = v___y_4250_;
v___y_4136_ = v___x_4264_;
v___y_4137_ = v___y_4251_;
v___y_4138_ = v___y_4252_;
v___y_4139_ = v___y_4253_;
v___y_4140_ = v___y_4254_;
v___y_4141_ = v___y_4255_;
v___y_4142_ = v___y_4256_;
v___y_4143_ = v___x_4269_;
v___y_4144_ = v___x_4266_;
v___y_4145_ = v___y_4257_;
v___y_4146_ = v___x_4262_;
v___y_4147_ = v___x_4268_;
v___y_4148_ = v___y_4259_;
v___y_4149_ = v___x_4274_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4275_; 
lean_dec(v___y_4258_);
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4130_ = v___y_4246_;
v___y_4131_ = v___y_4247_;
v___y_4132_ = v___y_4248_;
v___y_4133_ = v___y_4249_;
v___y_4134_ = v___x_4267_;
v___y_4135_ = v___y_4250_;
v___y_4136_ = v___x_4264_;
v___y_4137_ = v___y_4251_;
v___y_4138_ = v___y_4252_;
v___y_4139_ = v___y_4253_;
v___y_4140_ = v___y_4254_;
v___y_4141_ = v___y_4255_;
v___y_4142_ = v___y_4256_;
v___y_4143_ = v___x_4269_;
v___y_4144_ = v___x_4266_;
v___y_4145_ = v___y_4257_;
v___y_4146_ = v___x_4262_;
v___y_4147_ = v___x_4268_;
v___y_4148_ = v___y_4259_;
v___y_4149_ = v___x_4275_;
goto v___jp_4129_;
}
}
v___jp_4276_:
{
if (lean_obj_tag(v___y_4281_) == 0)
{
uint8_t v___x_4291_; 
v___x_4291_ = 0;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4283_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4290_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___x_4291_;
goto v___jp_4245_;
}
else
{
if (v___y_4283_ == 0)
{
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4283_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4290_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___y_4283_;
goto v___jp_4245_;
}
else
{
lean_object* v_ref_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_ref_4292_ = lean_ctor_get(v___y_4287_, 5);
v___x_4293_ = 0;
v___x_4294_ = l_Lean_SourceInfo_fromRef(v_ref_4292_, v___x_4293_);
v___x_4295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4296_ = l_Lean_Name_mkStr4(v___x_3941_, v___x_3942_, v___x_3943_, v___x_4295_);
v___x_4297_ = l_Lean_SourceInfo_fromRef(v_tk_3955_, v___x_3940_);
v___x_4298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4301_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4294_);
v___x_4302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4294_);
lean_ctor_set(v___x_4302_, 1, v___x_4300_);
lean_ctor_set(v___x_4302_, 2, v___x_4301_);
if (lean_obj_tag(v___y_4288_) == 1)
{
lean_object* v_val_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_val_4303_ = lean_ctor_get(v___y_4288_, 0);
lean_inc(v_val_4303_);
lean_dec_ref_known(v___y_4288_, 1);
v___x_4304_ = l_Lean_SourceInfo_fromRef(v_val_4303_, v___x_3940_);
lean_dec(v_val_4303_);
v___x_4305_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = l_Array_mkArray1___redArg(v___x_4306_);
v___y_4214_ = v___y_4277_;
v___y_4215_ = v___y_4278_;
v___y_4216_ = v___y_4279_;
v___y_4217_ = v___y_4280_;
v___y_4218_ = v___y_4281_;
v___y_4219_ = v___x_4294_;
v___y_4220_ = v___y_4282_;
v___y_4221_ = v___y_4283_;
v___y_4222_ = v___x_4300_;
v___y_4223_ = v___y_4284_;
v___y_4224_ = v___y_4286_;
v___y_4225_ = v___y_4285_;
v___y_4226_ = v___y_4287_;
v___y_4227_ = v___x_4299_;
v___y_4228_ = v___x_4302_;
v___y_4229_ = v___y_4290_;
v___y_4230_ = v___x_4301_;
v___y_4231_ = v___x_4296_;
v___y_4232_ = v___y_4289_;
v___y_4233_ = v___x_4307_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4308_; 
lean_dec(v___y_4288_);
v___x_4308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4214_ = v___y_4277_;
v___y_4215_ = v___y_4278_;
v___y_4216_ = v___y_4279_;
v___y_4217_ = v___y_4280_;
v___y_4218_ = v___y_4281_;
v___y_4219_ = v___x_4294_;
v___y_4220_ = v___y_4282_;
v___y_4221_ = v___y_4283_;
v___y_4222_ = v___x_4300_;
v___y_4223_ = v___y_4284_;
v___y_4224_ = v___y_4286_;
v___y_4225_ = v___y_4285_;
v___y_4226_ = v___y_4287_;
v___y_4227_ = v___x_4299_;
v___y_4228_ = v___x_4302_;
v___y_4229_ = v___y_4290_;
v___y_4230_ = v___x_4301_;
v___y_4231_ = v___x_4296_;
v___y_4232_ = v___y_4289_;
v___y_4233_ = v___x_4308_;
goto v___jp_4213_;
}
}
}
}
v___jp_4309_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4324_ = lean_unsigned_to_nat(3u);
v___x_4325_ = l_Lean_Syntax_getArg(v___y_4313_, v___x_4324_);
lean_dec(v___y_4313_);
v___x_4326_ = l_Lean_Syntax_getOptional_x3f(v___x_4325_);
lean_dec(v___x_4325_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_box(0);
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4316_;
v___y_4279_ = v___y_4317_;
v___y_4280_ = v___y_4319_;
v___y_4281_ = v___y_4310_;
v___y_4282_ = v_args_4315_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4318_;
v___y_4287_ = v___y_4322_;
v___y_4288_ = v___y_4312_;
v___y_4289_ = v___y_4314_;
v___y_4290_ = v___x_4327_;
goto v___jp_4276_;
}
else
{
lean_object* v_val_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
v_val_4328_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4326_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_val_4328_);
lean_dec(v___x_4326_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_val_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4316_;
v___y_4279_ = v___y_4317_;
v___y_4280_ = v___y_4319_;
v___y_4281_ = v___y_4310_;
v___y_4282_ = v_args_4315_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4318_;
v___y_4287_ = v___y_4322_;
v___y_4288_ = v___y_4312_;
v___y_4289_ = v___y_4314_;
v___y_4290_ = v___x_4333_;
goto v___jp_4276_;
}
}
}
}
v___jp_4337_:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = l_Lean_Syntax_getArg(v___y_4341_, v___y_4339_);
v___x_4353_ = l_Lean_Syntax_isNone(v___x_4352_);
if (v___x_4353_ == 0)
{
uint8_t v___x_4354_; 
lean_inc(v___x_4352_);
v___x_4354_ = l_Lean_Syntax_matchesNull(v___x_4352_, v___x_4336_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
lean_dec(v___x_4352_);
lean_dec(v_o_4343_);
lean_dec(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec(v___y_4338_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4356_ = l_Lean_Syntax_getArg(v___x_4352_, v___x_3954_);
lean_dec(v___x_4352_);
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3943_);
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
v___x_4358_ = l_Lean_Name_mkStr4(v___x_3941_, v___x_3942_, v___x_3943_, v___x_4357_);
lean_inc(v___x_4356_);
v___x_4359_ = l_Lean_Syntax_isOfKind(v___x_4356_, v___x_4358_);
lean_dec(v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec(v___x_4356_);
lean_dec(v_o_4343_);
lean_dec(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec(v___y_4338_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; lean_object* v_args_4362_; lean_object* v___x_4363_; 
v___x_4361_ = l_Lean_Syntax_getArg(v___x_4356_, v___x_4336_);
lean_dec(v___x_4356_);
v_args_4362_ = l_Lean_Syntax_getArgs(v___x_4361_);
lean_dec(v___x_4361_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v_args_4362_);
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v_o_4343_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v_args_4315_ = v___x_4363_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
v___y_4323_ = v___y_4351_;
goto v___jp_4309_;
}
}
}
else
{
lean_object* v___x_4364_; 
lean_dec(v___x_4352_);
v___x_4364_ = lean_box(0);
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v_o_4343_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v_args_4315_ = v___x_4364_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
v___y_4323_ = v___y_4351_;
goto v___jp_4309_;
}
}
v___jp_4365_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4375_ = lean_unsigned_to_nat(2u);
v___x_4376_ = l_Lean_Syntax_getArg(v_stx_3939_, v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3943_);
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
v___x_4378_ = l_Lean_Name_mkStr4(v___x_3941_, v___x_3942_, v___x_3943_, v___x_4377_);
lean_inc(v___x_4376_);
v___x_4379_ = l_Lean_Syntax_isOfKind(v___x_4376_, v___x_4378_);
lean_dec(v___x_4378_);
if (v___x_4379_ == 0)
{
lean_object* v___x_4380_; 
lean_dec(v___x_4376_);
lean_dec(v_bang_4366_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4380_;
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4381_ = l_Lean_Syntax_getArg(v___x_4376_, v___x_3954_);
v___x_4382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3943_);
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
v___x_4383_ = l_Lean_Name_mkStr4(v___x_3941_, v___x_3942_, v___x_3943_, v___x_4382_);
lean_inc(v___x_4381_);
v___x_4384_ = l_Lean_Syntax_isOfKind(v___x_4381_, v___x_4383_);
lean_dec(v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
lean_dec(v___x_4381_);
lean_dec(v___x_4376_);
lean_dec(v_bang_4366_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4385_;
}
else
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = l_Lean_Syntax_getArg(v___x_4376_, v___x_4336_);
v___x_4387_ = l_Lean_Syntax_isNone(v___x_4386_);
if (v___x_4387_ == 0)
{
uint8_t v___x_4388_; 
lean_inc(v___x_4386_);
v___x_4388_ = l_Lean_Syntax_matchesNull(v___x_4386_, v___x_4336_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; 
lean_dec(v___x_4386_);
lean_dec(v___x_4381_);
lean_dec(v___x_4376_);
lean_dec(v_bang_4366_);
lean_dec(v_tk_3955_);
lean_dec_ref(v___x_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
v___x_4389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4389_;
}
else
{
lean_object* v_o_4390_; lean_object* v___x_4391_; 
v_o_4390_ = l_Lean_Syntax_getArg(v___x_4386_, v___x_3954_);
lean_dec(v___x_4386_);
v___x_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_o_4390_);
v___y_4338_ = v_bang_4366_;
v___y_4339_ = v___x_4375_;
v___y_4340_ = v___x_4384_;
v___y_4341_ = v___x_4376_;
v___y_4342_ = v___x_4381_;
v_o_4343_ = v___x_4391_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
v___y_4351_ = v___y_4374_;
goto v___jp_4337_;
}
}
else
{
lean_object* v___x_4392_; 
lean_dec(v___x_4386_);
v___x_4392_ = lean_box(0);
v___y_4338_ = v_bang_4366_;
v___y_4339_ = v___x_4375_;
v___y_4340_ = v___x_4384_;
v___y_4341_ = v___x_4376_;
v___y_4342_ = v___x_4381_;
v_o_4343_ = v___x_4392_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
v___y_4351_ = v___y_4374_;
goto v___jp_4337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4400_, lean_object* v_stx_4401_, lean_object* v___x_4402_, lean_object* v___x_4403_, lean_object* v___x_4404_, lean_object* v___x_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
uint8_t v___x_10541__boxed_4415_; uint8_t v___x_10542__boxed_4416_; lean_object* v_res_4417_; 
v___x_10541__boxed_4415_ = lean_unbox(v___x_4400_);
v___x_10542__boxed_4416_ = lean_unbox(v___x_4402_);
v_res_4417_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10541__boxed_4415_, v_stx_4401_, v___x_10542__boxed_4416_, v___x_4403_, v___x_4404_, v___x_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v_stx_4401_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; uint8_t v___x_4438_; uint8_t v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___y_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4437_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4424_);
v___x_4438_ = l_Lean_Syntax_isOfKind(v_stx_4424_, v___x_4437_);
v___x_4439_ = 1;
v___x_4440_ = lean_box(v___x_4438_);
v___x_4441_ = lean_box(v___x_4439_);
v___y_4442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4442_, 0, v___x_4440_);
lean_closure_set(v___y_4442_, 1, v_stx_4424_);
lean_closure_set(v___y_4442_, 2, v___x_4441_);
lean_closure_set(v___y_4442_, 3, v___x_4434_);
lean_closure_set(v___y_4442_, 4, v___x_4435_);
lean_closure_set(v___y_4442_, 5, v___x_4436_);
v___x_4443_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4443_, 0, v___y_4442_);
v___x_4444_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4443_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4463_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4464_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4466_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4467_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4463_, v___x_4464_, v___x_4465_, v___x_4466_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4498_ = l_Lean_addBuiltinDeclarationRanges(v___x_4496_, v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4500_;
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
