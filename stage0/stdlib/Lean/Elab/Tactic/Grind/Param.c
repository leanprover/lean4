// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Param
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.Grind.ForallProp import Lean.Elab.Tactic.Grind.Anchor import Lean.Elab.SyntheticMVars
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "this parameter is redundant, environment already contains `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` annotated with `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected modifier "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7;
lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "redundant modifier `!` in `grind` parameter"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to generate equation theorems for `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid `grind` parameter, `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "` is a definition, the only acceptable (and redundant) modifier is '='"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` is a reducible definition, `grind` automatically unfolds them"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is not a theorem, definition, or inductive type"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__9;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_backward_grind_inferPattern;
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0;
lean_object* l_Lean_Elab_Tactic_Grind_elabAnchorRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "invalid `grind` parameter, only global declarations are allowed when `+revert` is used"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 97, 194, 195, 68, 28, 219, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "invalid `grind` parameter, failed to infer patterns"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "invalid `grind` parameter, parameter type is not a `forall` and is universe polymorphic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "invalid `grind` parameter, modifier is redundant since the parameter type is not a `forall`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid `grind` parameter, proof term expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0_value;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2_value;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3;
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0_value;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid use of `usr` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` does not have patterns specified with the command `grind_pattern`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`cases` parameter are not supported here"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid use of `intro` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`[grind ext]` cannot be set using parameters"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "normalization theorems should be registered using the `@[grind norm]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "declarations to be unfolded during normalization should be registered using the `@[grind unfold]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid use of modifier in `grind` attribute `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "redundant parameter `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`, `grind` uses local hypotheses automatically"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unexpected `grind` parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 172, 113, 174, 15, 5, 26, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid anchor, `only` modifier expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "invalid `-` occurrence, it can only used at the `grind` tactic entry point"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isMatchEqLikeDeclName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_16; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_1, 8);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 6);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 5);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = lean_array_fget(x_5, x_13);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_5, x_13, x_29);
x_31 = l_Lean_Meta_Grind_CasesTypes_insert(x_28, x_2, x_3);
lean_ctor_set(x_26, 0, x_31);
x_32 = lean_array_fset(x_30, x_13, x_26);
lean_ctor_set(x_1, 1, x_32);
return x_1;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
x_35 = lean_ctor_get(x_26, 2);
x_36 = lean_ctor_get(x_26, 3);
x_37 = lean_ctor_get(x_26, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_38 = lean_box(0);
x_39 = lean_array_fset(x_5, x_13, x_38);
x_40 = l_Lean_Meta_Grind_CasesTypes_insert(x_33, x_2, x_3);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_37);
x_42 = lean_array_fset(x_39, x_13, x_41);
lean_ctor_set(x_1, 1, x_42);
return x_1;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_43 = lean_array_fget(x_5, x_13);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
x_51 = lean_array_fset(x_5, x_13, x_50);
x_52 = l_Lean_Meta_Grind_CasesTypes_insert(x_44, x_2, x_3);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 5, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_48);
x_54 = lean_array_fset(x_51, x_13, x_53);
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_6);
lean_ctor_set(x_55, 3, x_7);
lean_ctor_set(x_55, 4, x_8);
lean_ctor_set(x_55, 5, x_9);
lean_ctor_set(x_55, 6, x_10);
lean_ctor_set(x_55, 7, x_11);
lean_ctor_set(x_55, 8, x_12);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_Grind_CasesTypes_contains(x_7, x_1);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 8);
lean_inc(x_27);
lean_dec_ref(x_1);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_20);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
goto block_54;
}
else
{
if (x_57 == 0)
{
goto block_54;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_56);
x_60 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(x_2, x_20, x_58, x_59);
if (x_60 == 0)
{
goto block_54;
}
else
{
x_28 = lean_box(0);
goto block_49;
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_7);
lean_ctor_set(x_16, 5, x_6);
lean_ctor_set(x_16, 6, x_11);
lean_ctor_set(x_16, 7, x_8);
lean_ctor_set(x_16, 8, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_49:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_20);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_2);
x_6 = x_24;
x_7 = x_23;
x_8 = x_26;
x_9 = x_22;
x_10 = x_21;
x_11 = x_25;
x_12 = x_19;
x_13 = lean_box(0);
x_14 = x_27;
x_15 = x_20;
goto block_18;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_array_fget(x_20, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_20, x_29, x_35);
x_37 = l_Lean_Meta_Grind_CasesTypes_erase(x_34, x_2);
lean_dec(x_2);
lean_ctor_set(x_32, 0, x_37);
x_38 = lean_array_fset(x_36, x_29, x_32);
x_6 = x_24;
x_7 = x_23;
x_8 = x_26;
x_9 = x_22;
x_10 = x_21;
x_11 = x_25;
x_12 = x_19;
x_13 = lean_box(0);
x_14 = x_27;
x_15 = x_38;
goto block_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
x_41 = lean_ctor_get(x_32, 2);
x_42 = lean_ctor_get(x_32, 3);
x_43 = lean_ctor_get(x_32, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_44 = lean_box(0);
x_45 = lean_array_fset(x_20, x_29, x_44);
x_46 = l_Lean_Meta_Grind_CasesTypes_erase(x_39, x_2);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_43);
x_48 = lean_array_fset(x_45, x_29, x_47);
x_6 = x_24;
x_7 = x_23;
x_8 = x_26;
x_9 = x_22;
x_10 = x_21;
x_11 = x_25;
x_12 = x_19;
x_13 = lean_box(0);
x_14 = x_27;
x_15 = x_48;
goto block_18;
}
}
}
block_54:
{
lean_object* x_50; 
lean_inc(x_2);
x_50 = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_28 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_51; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_15; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_1, 8);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_4, x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 2);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_4, x_12, x_28);
x_30 = l_Lean_NameSet_insert(x_27, x_2);
lean_ctor_set(x_25, 2, x_30);
x_31 = lean_array_fset(x_29, x_12, x_25);
lean_ctor_set(x_1, 1, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
x_34 = lean_ctor_get(x_25, 2);
x_35 = lean_ctor_get(x_25, 3);
x_36 = lean_ctor_get(x_25, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_4, x_12, x_37);
x_39 = l_Lean_NameSet_insert(x_34, x_2);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_36);
x_41 = lean_array_fset(x_38, x_12, x_40);
lean_ctor_set(x_1, 1, x_41);
return x_1;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_42 = lean_array_fget(x_4, x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc_ref(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_array_fset(x_4, x_12, x_49);
x_51 = l_Lean_NameSet_insert(x_45, x_2);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 5, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
x_53 = lean_array_fset(x_50, x_12, x_52);
x_54 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_5);
lean_ctor_set(x_54, 3, x_6);
lean_ctor_set(x_54, 4, x_7);
lean_ctor_set(x_54, 5, x_8);
lean_ctor_set(x_54, 6, x_9);
lean_ctor_set(x_54, 7, x_10);
lean_ctor_set(x_54, 8, x_11);
return x_54;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_Grind_Theorems_contains___redArg(x_7, x_8);
lean_dec_ref(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(x_2, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_Grind_Theorems_contains___redArg(x_7, x_8);
lean_dec_ref(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(x_2, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_15; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_1, 8);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_4, x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 3);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_4, x_12, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_27, x_30);
lean_ctor_set(x_25, 3, x_31);
x_32 = lean_array_fset(x_29, x_12, x_25);
lean_ctor_set(x_1, 1, x_32);
return x_1;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 3);
x_37 = lean_ctor_get(x_25, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = lean_array_fset(x_4, x_12, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_36, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_37);
x_43 = lean_array_fset(x_39, x_12, x_42);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_44 = lean_array_fget(x_4, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_44, 4);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
x_52 = lean_array_fset(x_4, x_12, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_48, x_53);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_49);
x_56 = lean_array_fset(x_52, x_12, x_55);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_5);
lean_ctor_set(x_57, 3, x_6);
lean_ctor_set(x_57, 4, x_7);
lean_ctor_set(x_57, 5, x_8);
lean_ctor_set(x_57, 6, x_9);
lean_ctor_set(x_57, 7, x_10);
lean_ctor_set(x_57, 8, x_11);
return x_57;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_7 = 1;
x_8 = lean_array_uget(x_3, x_4);
x_9 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(x_1, x_8);
if (x_9 == 0)
{
return x_7;
}
else
{
if (x_2 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_st_ref_get(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l_Lean_wasOriginallyTheorem(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_2);
x_15 = l_Lean_Meta_getEqnsFor_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_18);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_19 = lean_box(0);
goto block_34;
}
else
{
if (x_37 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_19 = lean_box(0);
goto block_34;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_36);
x_40 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(x_1, x_14, x_18, x_38, x_39);
if (x_40 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_19 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(x_2, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_19 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
block_34:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
if (x_22 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_21);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(x_18, x_26, x_27, x_1);
lean_dec(x_18);
if (lean_is_scalar(x_17)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_17;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_21);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(x_18, x_30, x_31, x_1);
lean_dec(x_18);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_1);
x_45 = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(x_2, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(x_1, x_2);
if (x_49 == 0)
{
lean_object* x_50; 
lean_inc(x_2);
x_50 = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(x_2, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_8 = lean_box(0);
goto block_11;
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(x_1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_15; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_1, 8);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_4, x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 4);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_4, x_12, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_27, x_30);
lean_ctor_set(x_25, 4, x_31);
x_32 = lean_array_fset(x_29, x_12, x_25);
lean_ctor_set(x_1, 1, x_32);
return x_1;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 3);
x_37 = lean_ctor_get(x_25, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = lean_array_fset(x_4, x_12, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_37, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_array_fset(x_39, x_12, x_42);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_44 = lean_array_fget(x_4, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_44, 4);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
x_52 = lean_array_fset(x_4, x_12, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = l_Lean_Meta_Grind_Theorems_erase___redArg(x_49, x_53);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_48);
lean_ctor_set(x_55, 4, x_54);
x_56 = lean_array_fset(x_52, x_12, x_55);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_5);
lean_ctor_set(x_57, 3, x_6);
lean_ctor_set(x_57, 4, x_7);
lean_ctor_set(x_57, 5, x_8);
lean_ctor_set(x_57, 6, x_9);
lean_ctor_set(x_57, 7, x_10);
lean_ctor_set(x_57, 8, x_11);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(x_13, x_1);
x_15 = l_List_isEmpty___redArg(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_List_appendTR___redArg(x_5, x_14);
x_6 = x_16;
goto block_10;
}
else
{
lean_dec(x_14);
x_6 = x_5;
goto block_10;
}
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(x_2, x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_4, x_1);
if (x_11 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_fget_borrowed(x_2, x_4);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
x_14 = l_Lean_Meta_Grind_Theorems_find___redArg(x_13, x_3);
x_15 = l_List_isEmpty___redArg(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_List_appendTR___redArg(x_5, x_14);
x_6 = x_16;
goto block_10;
}
else
{
lean_dec(x_14);
x_6 = x_5;
goto block_10;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(x_3, x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ExtensionStateArray_find(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_14);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_11);
lean_ctor_set(x_43, 2, x_15);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_53);
x_62 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_63 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (x_54 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_62;
x_12 = x_65;
x_13 = x_52;
x_14 = x_61;
x_15 = x_64;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_51;
x_11 = x_62;
x_12 = x_65;
x_13 = x_52;
x_14 = x_61;
x_15 = x_64;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_53);
x_69 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_70 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (x_54 == 0)
{
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_69;
x_12 = x_72;
x_13 = x_52;
x_14 = x_68;
x_15 = x_71;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_56);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_51;
x_11 = x_69;
x_12 = x_72;
x_13 = x_52;
x_14 = x_68;
x_15 = x_71;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_80, x_78);
lean_dec(x_80);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_81;
x_54 = x_82;
x_55 = x_84;
x_56 = x_83;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_81;
x_54 = x_82;
x_55 = x_84;
x_56 = x_83;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_92);
lean_dec(x_92);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_89);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_89;
x_79 = x_94;
x_80 = x_95;
x_81 = x_90;
x_82 = x_91;
x_83 = x_93;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_89;
x_79 = x_94;
x_80 = x_95;
x_81 = x_90;
x_82 = x_91;
x_83 = x_93;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_102;
x_89 = x_106;
x_90 = x_101;
x_91 = x_104;
x_92 = x_103;
x_93 = x_105;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_102;
x_89 = x_106;
x_90 = x_101;
x_91 = x_104;
x_92 = x_103;
x_93 = x_105;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc_ref(x_110);
lean_inc(x_113);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_117;
x_103 = x_113;
x_104 = x_114;
x_105 = x_110;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_warningAsError;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_112, x_120);
lean_inc_ref(x_110);
lean_inc(x_113);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_117;
x_103 = x_113;
x_104 = x_114;
x_105 = x_110;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = 0;
x_9 = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 0;
x_8 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
x_9 = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_5, x_7);
lean_dec(x_5);
x_10 = l_Lean_stringToMessageData(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
x_17 = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_13, x_15);
lean_dec(x_13);
x_18 = l_Lean_stringToMessageData(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; lean_object* x_36; 
lean_inc(x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(x_1, x_35);
lean_dec_ref(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
x_41 = 0;
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_36, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_36, 0);
lean_dec(x_56);
x_57 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
x_58 = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_39, x_41);
lean_dec(x_39);
x_59 = l_Lean_stringToMessageData(x_58);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_59);
lean_ctor_set(x_36, 0, x_57);
x_8 = x_36;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_36);
x_60 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
x_61 = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_39, x_41);
lean_dec(x_39);
x_62 = l_Lean_stringToMessageData(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_8 = x_63;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_40, 0);
switch (lean_obj_tag(x_64)) {
case 1:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec_ref(x_40);
if (lean_obj_tag(x_65) == 0)
{
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_66; 
lean_dec_ref(x_36);
x_66 = lean_ctor_get_uint8(x_39, 0);
lean_dec_ref(x_39);
x_42 = x_66;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = lean_box(0);
goto block_53;
}
else
{
lean_dec(x_39);
x_24 = x_36;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = lean_box(0);
goto block_34;
}
}
else
{
lean_dec(x_65);
lean_dec(x_39);
x_24 = x_36;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = lean_box(0);
goto block_34;
}
}
case 0:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_40, 1);
lean_inc(x_67);
lean_dec_ref(x_40);
if (lean_obj_tag(x_67) == 0)
{
if (lean_obj_tag(x_39) == 1)
{
uint8_t x_68; 
lean_dec_ref(x_36);
x_68 = lean_ctor_get_uint8(x_39, 0);
lean_dec_ref(x_39);
x_42 = x_68;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = lean_box(0);
goto block_53;
}
else
{
lean_dec(x_39);
x_24 = x_36;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = lean_box(0);
goto block_34;
}
}
else
{
lean_dec(x_67);
lean_dec(x_39);
x_24 = x_36;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = lean_box(0);
goto block_34;
}
}
default: 
{
lean_dec_ref(x_40);
lean_dec(x_39);
x_24 = x_36;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = lean_box(0);
goto block_34;
}
}
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
x_49 = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(x_49, 0, x_42);
x_50 = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_49, x_41);
lean_dec_ref(x_49);
x_51 = l_Lean_stringToMessageData(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_8 = x_52;
x_9 = x_43;
x_10 = x_44;
x_11 = x_45;
x_12 = x_46;
x_13 = lean_box(0);
goto block_23;
}
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1;
x_15 = l_Lean_MessageData_ofName(x_2);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(x_21, x_9, x_10, x_11, x_12);
return x_22;
}
block_34:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_box(0);
x_31 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(x_24, x_30);
x_32 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(x_31, x_30);
x_33 = l_Lean_MessageData_ofList(x_32);
x_8 = x_33;
x_9 = x_25;
x_10 = x_26;
x_11 = x_27;
x_12 = x_28;
x_13 = lean_box(0);
goto block_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
x_8 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(x_1);
x_9 = l_Lean_Parser_runParserCategory(x_6, x_7, x_1, x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Meta_Grind_getAttrKindCore(x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_9);
x_12 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7;
x_13 = l_Lean_stringToMessageData(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(x_14, x_2, x_3);
lean_dec_ref(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1;
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2;
x_14 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6;
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_box(0);
x_30 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_31 = l_Lean_EnvironmentHeader_moduleNames(x_30);
x_32 = lean_array_get(x_29, x_31, x_28);
lean_dec(x_28);
lean_dec_ref(x_31);
x_33 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_18);
x_36 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofName(x_32);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_note(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_18);
x_46 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofName(x_32);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_note(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_53);
return x_19;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
lean_dec(x_19);
x_55 = lean_box(0);
x_56 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_57 = l_Lean_EnvironmentHeader_moduleNames(x_56);
x_58 = lean_array_get(x_55, x_57, x_54);
lean_dec(x_54);
lean_dec_ref(x_57);
x_59 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_18);
x_62 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofName(x_58);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MessageData_note(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_18);
x_73 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofName(x_58);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_note(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_1);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_unknownIdentifierMessageTag;
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_unknownIdentifierMessageTag;
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*14);
x_25 = lean_ctor_get(x_5, 12);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_27 = lean_ctor_get(x_5, 13);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_28 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_16);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_18);
lean_ctor_set(x_29, 7, x_19);
lean_ctor_set(x_29, 8, x_20);
lean_ctor_set(x_29, 9, x_21);
lean_ctor_set(x_29, 10, x_22);
lean_ctor_set(x_29, 11, x_23);
lean_ctor_set(x_29, 12, x_25);
lean_ctor_set(x_29, 13, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*14, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*14 + 1, x_26);
x_30 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_2, x_3, x_4, x_29, x_6);
lean_dec_ref(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_1, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
x_9 = 0;
lean_inc(x_2);
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_Environment_findAsync_x3f(x_9, x_1, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_ctor_set_tag(x_10, 0);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_get_reducibility_status(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(x_1, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_265; 
x_65 = 0;
lean_inc_ref(x_10);
lean_inc(x_3);
x_265 = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(x_3, x_65, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = lean_ctor_get_uint8(x_266, sizeof(void*)*3);
lean_dec(x_266);
switch (x_267) {
case 1:
{
x_181 = x_8;
x_182 = x_9;
x_183 = x_10;
x_184 = x_11;
x_185 = lean_box(0);
goto block_264;
}
case 2:
{
x_181 = x_8;
x_182 = x_9;
x_183 = x_10;
x_184 = x_11;
x_185 = lean_box(0);
goto block_264;
}
case 6:
{
x_181 = x_8;
x_182 = x_9;
x_183 = x_10;
x_184 = x_11;
x_185 = lean_box(0);
goto block_264;
}
case 0:
{
lean_object* x_268; 
lean_dec(x_2);
lean_inc(x_3);
x_268 = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(x_3, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
lean_dec_ref(x_268);
x_270 = lean_unbox(x_269);
lean_dec(x_269);
if (x_270 == 0)
{
x_127 = x_8;
x_128 = x_9;
x_129 = x_10;
x_130 = x_11;
x_131 = lean_box(0);
goto block_143;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_271 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_272 = l_Lean_MessageData_ofConstName(x_3, x_65);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__7;
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_275, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
return x_276;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_280 = !lean_is_exclusive(x_268);
if (x_280 == 0)
{
return x_268;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_268, 0);
lean_inc(x_281);
lean_dec(x_268);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
default: 
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_283 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__3;
x_284 = l_Lean_MessageData_ofConstName(x_3, x_65);
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__9;
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_287, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_289 = !lean_is_exclusive(x_265);
if (x_289 == 0)
{
return x_265;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_265, 0);
lean_inc(x_290);
lean_dec(x_265);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
block_31:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_PersistentArray_push___redArg(x_16, x_13);
lean_ctor_set(x_1, 2, x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = lean_ctor_get(x_1, 4);
x_24 = lean_ctor_get(x_1, 5);
x_25 = lean_ctor_get(x_1, 6);
x_26 = lean_ctor_get(x_1, 7);
x_27 = lean_ctor_get(x_1, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_13);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_22);
lean_ctor_set(x_29, 4, x_23);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set(x_29, 6, x_25);
lean_ctor_set(x_29, 7, x_26);
lean_ctor_set(x_29, 8, x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
block_47:
{
if (x_7 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_3);
x_13 = x_32;
x_14 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_32, 3);
x_40 = lean_ctor_get(x_32, 5);
x_41 = lean_ctor_get(x_32, 7);
lean_inc(x_41);
lean_inc(x_39);
x_42 = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(x_38, x_40, x_39, x_41);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_3);
x_13 = x_32;
x_14 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_43; 
x_43 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(x_38, x_3, x_33, x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_13 = x_32;
x_14 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_32);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
block_64:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lean_PersistentArray_push___redArg(x_53, x_51);
x_61 = l_Lean_PersistentArray_push___redArg(x_60, x_56);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_55);
lean_ctor_set(x_62, 5, x_49);
lean_ctor_set(x_62, 6, x_48);
lean_ctor_set(x_62, 7, x_54);
lean_ctor_set(x_62, 8, x_58);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
block_126:
{
lean_object* x_71; 
x_71 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec_ref(x_71);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc(x_3);
x_72 = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(x_3, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_1, 2);
x_78 = l_Array_toPArray_x27___redArg(x_75);
lean_dec(x_75);
x_79 = l_Lean_PersistentArray_append___redArg(x_77, x_78);
lean_dec_ref(x_78);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_72, 0, x_1);
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 1);
x_82 = lean_ctor_get(x_1, 2);
x_83 = lean_ctor_get(x_1, 3);
x_84 = lean_ctor_get(x_1, 4);
x_85 = lean_ctor_get(x_1, 5);
x_86 = lean_ctor_get(x_1, 6);
x_87 = lean_ctor_get(x_1, 7);
x_88 = lean_ctor_get(x_1, 8);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_1);
x_89 = l_Array_toPArray_x27___redArg(x_75);
lean_dec(x_75);
x_90 = l_Lean_PersistentArray_append___redArg(x_82, x_89);
lean_dec_ref(x_89);
x_91 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_83);
lean_ctor_set(x_91, 4, x_84);
lean_ctor_set(x_91, 5, x_85);
lean_ctor_set(x_91, 6, x_86);
lean_ctor_set(x_91, 7, x_87);
lean_ctor_set(x_91, 8, x_88);
lean_ctor_set(x_72, 0, x_91);
return x_72;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_72);
lean_dec(x_74);
lean_dec_ref(x_1);
x_92 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__1;
x_93 = l_Lean_MessageData_ofConstName(x_3, x_65);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_96, x_66, x_67, x_68, x_69);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
return x_97;
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_72, 0);
lean_inc(x_98);
lean_dec(x_72);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_3);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_1, 8);
lean_inc(x_108);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_109 = x_1;
} else {
 lean_dec_ref(x_1);
 x_109 = lean_box(0);
}
x_110 = l_Array_toPArray_x27___redArg(x_99);
lean_dec(x_99);
x_111 = l_Lean_PersistentArray_append___redArg(x_102, x_110);
lean_dec_ref(x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 9, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_101);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_103);
lean_ctor_set(x_112, 4, x_104);
lean_ctor_set(x_112, 5, x_105);
lean_ctor_set(x_112, 6, x_106);
lean_ctor_set(x_112, 7, x_107);
lean_ctor_set(x_112, 8, x_108);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_98);
lean_dec_ref(x_1);
x_114 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__1;
x_115 = l_Lean_MessageData_ofConstName(x_3, x_65);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_118, x_66, x_67, x_68, x_69);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_3);
lean_dec_ref(x_1);
x_120 = !lean_is_exclusive(x_72);
if (x_120 == 0)
{
return x_72;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_72, 0);
lean_inc(x_121);
lean_dec(x_72);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_3);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_71);
if (x_123 == 0)
{
return x_71;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_71, 0);
lean_inc(x_124);
lean_dec(x_71);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
block_143:
{
uint8_t x_132; 
x_132 = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(x_4);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(x_4);
lean_dec(x_4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec_ref(x_1);
x_134 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__3;
x_135 = l_Lean_MessageData_ofConstName(x_3, x_65);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Elab_Tactic_addEMatchTheorem___closed__5;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_138, x_127, x_128, x_129, x_130);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
else
{
x_66 = x_127;
x_67 = x_128;
x_68 = x_129;
x_69 = x_130;
x_70 = lean_box(0);
goto block_126;
}
}
else
{
lean_dec(x_4);
x_66 = x_127;
x_67 = x_128;
x_68 = x_129;
x_69 = x_130;
x_70 = lean_box(0);
goto block_126;
}
}
block_155:
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_1, 5);
lean_inc(x_146);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc_ref(x_144);
lean_inc_ref(x_149);
lean_inc(x_3);
x_150 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_3, x_4, x_149, x_65, x_5, x_144, x_147, x_148, x_146);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_32 = x_151;
x_33 = x_144;
x_34 = x_147;
x_35 = x_148;
x_36 = x_146;
x_37 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_152; 
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_144);
lean_dec(x_3);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
return x_150;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
block_170:
{
if (x_6 == 0)
{
lean_dec(x_2);
x_144 = x_156;
x_145 = lean_box(0);
x_146 = x_159;
x_147 = x_157;
x_148 = x_158;
goto block_155;
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_158, 2);
x_162 = l_Lean_Meta_Grind_backward_grind_inferPattern;
x_163 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_4);
x_164 = lean_ctor_get(x_1, 5);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc_ref(x_156);
lean_inc_ref(x_164);
lean_inc(x_3);
x_165 = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(x_2, x_3, x_164, x_5, x_6, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_32 = x_166;
x_33 = x_156;
x_34 = x_157;
x_35 = x_158;
x_36 = x_159;
x_37 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_167; 
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_3);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
lean_dec(x_2);
x_144 = x_156;
x_145 = lean_box(0);
x_146 = x_159;
x_147 = x_157;
x_148 = x_158;
goto block_155;
}
}
}
block_180:
{
lean_object* x_176; 
x_176 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_171, x_173, x_175, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_dec_ref(x_176);
x_156 = x_171;
x_157 = x_173;
x_158 = x_175;
x_159 = x_174;
x_160 = lean_box(0);
goto block_170;
}
else
{
uint8_t x_177; 
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec_ref(x_171);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
return x_176;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
block_264:
{
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_186; 
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_4);
if (x_186 == 0)
{
uint8_t x_187; lean_object* x_188; 
x_187 = lean_ctor_get_uint8(x_4, 0);
x_188 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_188);
x_189 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_1, 8);
lean_inc(x_197);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_4, 0);
lean_inc(x_184);
lean_inc_ref(x_183);
lean_inc(x_182);
lean_inc_ref(x_181);
lean_inc_ref(x_194);
lean_inc(x_3);
x_198 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_3, x_4, x_194, x_65, x_65, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_200, 0, x_187);
lean_inc(x_184);
lean_inc_ref(x_183);
lean_inc(x_182);
lean_inc_ref(x_181);
lean_inc_ref(x_194);
lean_inc(x_3);
x_201 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_3, x_200, x_194, x_65, x_65, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_201) == 0)
{
if (x_7 == 0)
{
lean_object* x_202; 
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_48 = x_195;
x_49 = x_194;
x_50 = x_189;
x_51 = x_199;
x_52 = x_190;
x_53 = x_191;
x_54 = x_196;
x_55 = x_193;
x_56 = x_202;
x_57 = x_192;
x_58 = x_197;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
lean_dec_ref(x_201);
x_204 = lean_ctor_get(x_199, 3);
x_205 = lean_ctor_get(x_199, 5);
x_206 = lean_ctor_get(x_199, 7);
lean_inc(x_206);
lean_inc(x_204);
x_207 = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(x_190, x_205, x_204, x_206);
if (x_207 == 0)
{
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_48 = x_195;
x_49 = x_194;
x_50 = x_189;
x_51 = x_199;
x_52 = x_190;
x_53 = x_191;
x_54 = x_196;
x_55 = x_193;
x_56 = x_203;
x_57 = x_192;
x_58 = x_197;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_203, 3);
x_209 = lean_ctor_get(x_203, 5);
x_210 = lean_ctor_get(x_203, 7);
lean_inc(x_210);
lean_inc(x_208);
x_211 = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(x_190, x_209, x_208, x_210);
if (x_211 == 0)
{
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_48 = x_195;
x_49 = x_194;
x_50 = x_189;
x_51 = x_199;
x_52 = x_190;
x_53 = x_191;
x_54 = x_196;
x_55 = x_193;
x_56 = x_203;
x_57 = x_192;
x_58 = x_197;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_212; 
x_212 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(x_190, x_3, x_181, x_182, x_183, x_184);
lean_dec(x_184);
lean_dec(x_182);
lean_dec_ref(x_181);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_212);
x_48 = x_195;
x_49 = x_194;
x_50 = x_189;
x_51 = x_199;
x_52 = x_190;
x_53 = x_191;
x_54 = x_196;
x_55 = x_193;
x_56 = x_203;
x_57 = x_192;
x_58 = x_197;
x_59 = lean_box(0);
goto block_64;
}
else
{
uint8_t x_213; 
lean_dec(x_203);
lean_dec(x_199);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_189);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_189);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_201);
if (x_216 == 0)
{
return x_201;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_201, 0);
lean_inc(x_217);
lean_dec(x_201);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_189);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_219 = !lean_is_exclusive(x_198);
if (x_219 == 0)
{
return x_198;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_198, 0);
lean_inc(x_220);
lean_dec(x_198);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_free_object(x_4);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
lean_dec_ref(x_1);
x_222 = !lean_is_exclusive(x_188);
if (x_222 == 0)
{
return x_188;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_188, 0);
lean_inc(x_223);
lean_dec(x_188);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; lean_object* x_226; 
x_225 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_226 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_226);
x_227 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_232);
x_233 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_233);
x_234 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_1, 8);
lean_inc(x_235);
lean_dec_ref(x_1);
x_236 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_236, 0, x_225);
lean_inc(x_184);
lean_inc_ref(x_183);
lean_inc(x_182);
lean_inc_ref(x_181);
lean_inc_ref(x_232);
lean_inc(x_3);
x_237 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_3, x_236, x_232, x_65, x_65, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_239, 0, x_225);
lean_inc(x_184);
lean_inc_ref(x_183);
lean_inc(x_182);
lean_inc_ref(x_181);
lean_inc_ref(x_232);
lean_inc(x_3);
x_240 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_3, x_239, x_232, x_65, x_65, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_240) == 0)
{
if (x_7 == 0)
{
lean_object* x_241; 
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_48 = x_233;
x_49 = x_232;
x_50 = x_227;
x_51 = x_238;
x_52 = x_228;
x_53 = x_229;
x_54 = x_234;
x_55 = x_231;
x_56 = x_241;
x_57 = x_230;
x_58 = x_235;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec_ref(x_240);
x_243 = lean_ctor_get(x_238, 3);
x_244 = lean_ctor_get(x_238, 5);
x_245 = lean_ctor_get(x_238, 7);
lean_inc(x_245);
lean_inc(x_243);
x_246 = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(x_228, x_244, x_243, x_245);
if (x_246 == 0)
{
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_48 = x_233;
x_49 = x_232;
x_50 = x_227;
x_51 = x_238;
x_52 = x_228;
x_53 = x_229;
x_54 = x_234;
x_55 = x_231;
x_56 = x_242;
x_57 = x_230;
x_58 = x_235;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_247 = lean_ctor_get(x_242, 3);
x_248 = lean_ctor_get(x_242, 5);
x_249 = lean_ctor_get(x_242, 7);
lean_inc(x_249);
lean_inc(x_247);
x_250 = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(x_228, x_248, x_247, x_249);
if (x_250 == 0)
{
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_48 = x_233;
x_49 = x_232;
x_50 = x_227;
x_51 = x_238;
x_52 = x_228;
x_53 = x_229;
x_54 = x_234;
x_55 = x_231;
x_56 = x_242;
x_57 = x_230;
x_58 = x_235;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_251; 
x_251 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(x_228, x_3, x_181, x_182, x_183, x_184);
lean_dec(x_184);
lean_dec(x_182);
lean_dec_ref(x_181);
if (lean_obj_tag(x_251) == 0)
{
lean_dec_ref(x_251);
x_48 = x_233;
x_49 = x_232;
x_50 = x_227;
x_51 = x_238;
x_52 = x_228;
x_53 = x_229;
x_54 = x_234;
x_55 = x_231;
x_56 = x_242;
x_57 = x_230;
x_58 = x_235;
x_59 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_242);
lean_dec(x_238);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_238);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_255 = lean_ctor_get(x_240, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_256 = x_240;
} else {
 lean_dec_ref(x_240);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
x_258 = lean_ctor_get(x_237, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_259 = x_237;
} else {
 lean_dec_ref(x_237);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_3);
lean_dec_ref(x_1);
x_261 = lean_ctor_get(x_226, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_262 = x_226;
} else {
 lean_dec_ref(x_226);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
return x_263;
}
}
}
else
{
switch (lean_obj_tag(x_4)) {
case 0:
{
x_171 = x_181;
x_172 = lean_box(0);
x_173 = x_182;
x_174 = x_184;
x_175 = x_183;
goto block_180;
}
case 1:
{
x_171 = x_181;
x_172 = lean_box(0);
x_173 = x_182;
x_174 = x_184;
x_175 = x_183;
goto block_180;
}
default: 
{
x_156 = x_181;
x_157 = x_182;
x_158 = x_183;
x_159 = x_184;
x_160 = lean_box(0);
goto block_170;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = lean_unbox(x_7);
x_16 = l_Lean_Elab_Tactic_addEMatchTheorem(x_1, x_2, x_3, x_4, x_13, x_14, x_15, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 8);
lean_inc(x_14);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_15 = x_1;
} else {
 lean_dec_ref(x_1);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_32; 
x_32 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0;
x_16 = x_32;
goto block_31;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_33);
lean_dec_ref(x_14);
x_16 = x_33;
goto block_31;
}
block_31:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_Grind_elabAnchorRef(x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_push(x_16, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_15)) {
 x_22 = lean_alloc_ctor(0, 9, 0);
} else {
 x_22 = x_15;
}
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_10);
lean_ctor_set(x_22, 5, x_11);
lean_ctor_set(x_22, 6, x_12);
lean_ctor_set(x_22, 7, x_13);
lean_ctor_set(x_22, 8, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_array_push(x_16, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_15)) {
 x_26 = lean_alloc_ctor(0, 9, 0);
} else {
 x_26 = x_15;
}
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set(x_26, 2, x_8);
lean_ctor_set(x_26, 3, x_9);
lean_ctor_set(x_26, 4, x_10);
lean_ctor_set(x_26, 5, x_11);
lean_ctor_set(x_26, 6, x_12);
lean_ctor_set(x_26, 7, x_13);
lean_ctor_set(x_26, 8, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 28);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1;
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(x_9, x_2, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(x_1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Lean_Elab_Term_elabTerm(x_2, x_3, x_4, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = 1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec_ref(x_18);
x_19 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(x_16, x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Expr_hasSyntheticSorry(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_eta(x_21);
x_24 = l_Lean_Expr_hasMVar(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_25 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; 
lean_free_object(x_19);
x_28 = l_Lean_Meta_abstractMVars(x_23, x_4, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc_ref(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_35, 2);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_21);
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_44 = lean_box(0);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
x_46 = l_Lean_Expr_hasSyntheticSorry(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Expr_eta(x_45);
x_48 = l_Lean_Expr_hasMVar(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_49 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Meta_abstractMVars(x_47, x_4, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_45);
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_16);
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
return x_18;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
lean_dec(x_18);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
lean_dec(x_15);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
x_74 = lean_ctor_get(x_9, 2);
x_75 = lean_ctor_get(x_9, 3);
x_76 = lean_ctor_get(x_9, 4);
x_77 = lean_ctor_get(x_9, 5);
x_78 = lean_ctor_get(x_9, 6);
x_79 = lean_ctor_get(x_9, 7);
x_80 = lean_ctor_get(x_9, 8);
x_81 = lean_ctor_get(x_9, 9);
x_82 = lean_ctor_get(x_9, 10);
x_83 = lean_ctor_get(x_9, 11);
x_84 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_85 = lean_ctor_get(x_9, 12);
x_86 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_87 = lean_ctor_get(x_9, 13);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_88 = l_Lean_replaceRef(x_1, x_77);
lean_dec(x_77);
x_89 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_89, 0, x_72);
lean_ctor_set(x_89, 1, x_73);
lean_ctor_set(x_89, 2, x_74);
lean_ctor_set(x_89, 3, x_75);
lean_ctor_set(x_89, 4, x_76);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_78);
lean_ctor_set(x_89, 7, x_79);
lean_ctor_set(x_89, 8, x_80);
lean_ctor_set(x_89, 9, x_81);
lean_ctor_set(x_89, 10, x_82);
lean_ctor_set(x_89, 11, x_83);
lean_ctor_set(x_89, 12, x_85);
lean_ctor_set(x_89, 13, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*14, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*14 + 1, x_86);
lean_inc(x_10);
lean_inc_ref(x_89);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_90 = l_Lean_Elab_Term_elabTerm(x_2, x_3, x_4, x_4, x_5, x_6, x_7, x_8, x_89, x_10);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = 1;
lean_inc(x_10);
lean_inc_ref(x_89);
lean_inc(x_8);
lean_inc_ref(x_7);
x_93 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_92, x_4, x_5, x_6, x_7, x_8, x_89, x_10);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec_ref(x_93);
x_94 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(x_91, x_8);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = l_Lean_Expr_hasSyntheticSorry(x_95);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_Expr_eta(x_95);
x_99 = l_Lean_Expr_hasMVar(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_89);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_100 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 1, 0);
} else {
 x_103 = x_96;
}
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_96);
x_104 = l_Lean_Meta_abstractMVars(x_98, x_4, x_7, x_8, x_89, x_10);
lean_dec(x_10);
lean_dec_ref(x_89);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_105, 2);
lean_inc_ref(x_108);
lean_dec(x_105);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_104, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_113 = x_104;
} else {
 lean_dec_ref(x_104);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_95);
lean_dec_ref(x_89);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_115 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_96;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
lean_dec_ref(x_89);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_118 = x_93;
} else {
 lean_dec_ref(x_93);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_89);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_120 = lean_ctor_get(x_90, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_121 = x_90;
} else {
 lean_dec_ref(x_90);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
x_16 = lean_name_append_index_after(x_15, x_8);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_19 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_17, x_3, x_4, x_7, x_14, x_5, x_18, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_19);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3;
x_24 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_23, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3;
x_29 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(x_28, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(x_19, x_2);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(x_29, x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(x_11, x_12, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_65; lean_object* x_66; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_315; 
x_315 = !lean_is_exclusive(x_10);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_10, 5);
x_317 = l_Lean_replaceRef(x_2, x_316);
lean_dec(x_316);
lean_ctor_set(x_10, 5, x_317);
x_318 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(x_1, x_10, x_11);
if (lean_obj_tag(x_318) == 0)
{
lean_dec_ref(x_318);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
lean_inc(x_319);
x_320 = l_Lean_Meta_Grind_getAttrKindCore(x_319, x_10, x_11);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
switch (lean_obj_tag(x_321)) {
case 0:
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_321, 0);
lean_inc(x_334);
lean_dec_ref(x_321);
if (lean_obj_tag(x_334) == 9)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_322 = x_6;
x_323 = x_7;
x_324 = x_8;
x_325 = x_9;
x_326 = x_10;
x_327 = x_11;
goto block_333;
}
else
{
x_241 = x_334;
x_242 = x_6;
x_243 = x_7;
x_244 = x_8;
x_245 = x_9;
x_246 = x_10;
x_247 = x_11;
x_248 = lean_box(0);
goto block_305;
}
}
case 1:
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec_ref(x_321);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_335 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_336 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_335, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_337 = !lean_is_exclusive(x_336);
if (x_337 == 0)
{
return x_336;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
}
case 3:
{
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_10;
x_311 = x_11;
x_312 = lean_box(0);
goto block_314;
}
case 5:
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec_ref(x_321);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_340 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_341 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_340, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
return x_341;
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
}
case 8:
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_dec_ref(x_321);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_345 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_346 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_345, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
return x_346;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
}
default: 
{
lean_dec(x_321);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_322 = x_6;
x_323 = x_7;
x_324 = x_8;
x_325 = x_9;
x_326 = x_10;
x_327 = x_11;
goto block_333;
}
}
block_333:
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_328 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_329 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_328, x_322, x_323, x_324, x_325, x_326, x_327);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_323);
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
return x_329;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
}
}
else
{
uint8_t x_350; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_350 = !lean_is_exclusive(x_320);
if (x_350 == 0)
{
return x_320;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_320, 0);
lean_inc(x_351);
lean_dec(x_320);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
}
else
{
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_10;
x_311 = x_11;
x_312 = lean_box(0);
goto block_314;
}
}
else
{
uint8_t x_353; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_353 = !lean_is_exclusive(x_318);
if (x_353 == 0)
{
return x_318;
}
else
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_318, 0);
lean_inc(x_354);
lean_dec(x_318);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_354);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_356 = lean_ctor_get(x_10, 0);
x_357 = lean_ctor_get(x_10, 1);
x_358 = lean_ctor_get(x_10, 2);
x_359 = lean_ctor_get(x_10, 3);
x_360 = lean_ctor_get(x_10, 4);
x_361 = lean_ctor_get(x_10, 5);
x_362 = lean_ctor_get(x_10, 6);
x_363 = lean_ctor_get(x_10, 7);
x_364 = lean_ctor_get(x_10, 8);
x_365 = lean_ctor_get(x_10, 9);
x_366 = lean_ctor_get(x_10, 10);
x_367 = lean_ctor_get(x_10, 11);
x_368 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_369 = lean_ctor_get(x_10, 12);
x_370 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_371 = lean_ctor_get(x_10, 13);
lean_inc(x_371);
lean_inc(x_369);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_10);
x_372 = l_Lean_replaceRef(x_2, x_361);
lean_dec(x_361);
x_373 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_373, 0, x_356);
lean_ctor_set(x_373, 1, x_357);
lean_ctor_set(x_373, 2, x_358);
lean_ctor_set(x_373, 3, x_359);
lean_ctor_set(x_373, 4, x_360);
lean_ctor_set(x_373, 5, x_372);
lean_ctor_set(x_373, 6, x_362);
lean_ctor_set(x_373, 7, x_363);
lean_ctor_set(x_373, 8, x_364);
lean_ctor_set(x_373, 9, x_365);
lean_ctor_set(x_373, 10, x_366);
lean_ctor_set(x_373, 11, x_367);
lean_ctor_set(x_373, 12, x_369);
lean_ctor_set(x_373, 13, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*14, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*14 + 1, x_370);
x_374 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(x_1, x_373, x_11);
if (lean_obj_tag(x_374) == 0)
{
lean_dec_ref(x_374);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_373);
lean_inc(x_375);
x_376 = l_Lean_Meta_Grind_getAttrKindCore(x_375, x_373, x_11);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec_ref(x_376);
switch (lean_obj_tag(x_377)) {
case 0:
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_377, 0);
lean_inc(x_390);
lean_dec_ref(x_377);
if (lean_obj_tag(x_390) == 9)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_378 = x_6;
x_379 = x_7;
x_380 = x_8;
x_381 = x_9;
x_382 = x_373;
x_383 = x_11;
goto block_389;
}
else
{
x_241 = x_390;
x_242 = x_6;
x_243 = x_7;
x_244 = x_8;
x_245 = x_9;
x_246 = x_373;
x_247 = x_11;
x_248 = lean_box(0);
goto block_305;
}
}
case 1:
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec_ref(x_377);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_391 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_392 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_391, x_6, x_7, x_8, x_9, x_373, x_11);
lean_dec(x_11);
lean_dec_ref(x_373);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_394 = x_392;
} else {
 lean_dec_ref(x_392);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 1, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
return x_395;
}
case 3:
{
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_373;
x_311 = x_11;
x_312 = lean_box(0);
goto block_314;
}
case 5:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec_ref(x_377);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_396 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_397 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_396, x_6, x_7, x_8, x_9, x_373, x_11);
lean_dec(x_11);
lean_dec_ref(x_373);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 1, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_398);
return x_400;
}
case 8:
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec_ref(x_377);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_401 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_402 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_401, x_6, x_7, x_8, x_9, x_373, x_11);
lean_dec(x_11);
lean_dec_ref(x_373);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_404 = x_402;
} else {
 lean_dec_ref(x_402);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 1, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_403);
return x_405;
}
default: 
{
lean_dec(x_377);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_378 = x_6;
x_379 = x_7;
x_380 = x_8;
x_381 = x_9;
x_382 = x_373;
x_383 = x_11;
goto block_389;
}
}
block_389:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_384 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
x_385 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_384, x_378, x_379, x_380, x_381, x_382, x_383);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec_ref(x_380);
lean_dec(x_379);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_387 = x_385;
} else {
 lean_dec_ref(x_385);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec_ref(x_373);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_376, 0);
lean_inc(x_406);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 x_407 = x_376;
} else {
 lean_dec_ref(x_376);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_406);
return x_408;
}
}
else
{
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_373;
x_311 = x_11;
x_312 = lean_box(0);
goto block_314;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec_ref(x_373);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_409 = lean_ctor_get(x_374, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_410 = x_374;
} else {
 lean_dec_ref(x_374);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 1, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
return x_411;
}
}
block_42:
{
lean_object* x_30; 
x_30 = lean_apply_7(x_18, x_22, x_17, x_25, x_26, x_27, x_28, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_PersistentArray_push___redArg(x_21, x_32);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_24);
lean_ctor_set(x_34, 4, x_19);
lean_ctor_set(x_34, 5, x_16);
lean_ctor_set(x_34, 6, x_14);
lean_ctor_set(x_34, 7, x_13);
lean_ctor_set(x_34, 8, x_15);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_PersistentArray_push___redArg(x_21, x_35);
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_20);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set(x_37, 4, x_19);
lean_ctor_set(x_37, 5, x_16);
lean_ctor_set(x_37, 6, x_14);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_15);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
block_64:
{
lean_object* x_60; 
x_60 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_43, x_50, x_51, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_dec_ref(x_60);
x_13 = x_54;
x_14 = x_44;
x_15 = x_45;
x_16 = x_46;
x_17 = x_55;
x_18 = x_56;
x_19 = x_47;
x_20 = x_57;
x_21 = x_48;
x_22 = x_49;
x_23 = x_59;
x_24 = x_52;
x_25 = x_43;
x_26 = x_50;
x_27 = x_51;
x_28 = x_58;
x_29 = lean_box(0);
goto block_42;
}
else
{
uint8_t x_61; 
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
block_83:
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_1, 4);
x_69 = l_Lean_PersistentArray_push___redArg(x_68, x_65);
lean_ctor_set(x_1, 4, x_69);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_1, 1);
x_73 = lean_ctor_get(x_1, 2);
x_74 = lean_ctor_get(x_1, 3);
x_75 = lean_ctor_get(x_1, 4);
x_76 = lean_ctor_get(x_1, 5);
x_77 = lean_ctor_get(x_1, 6);
x_78 = lean_ctor_get(x_1, 7);
x_79 = lean_ctor_get(x_1, 8);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_1);
x_80 = l_Lean_PersistentArray_push___redArg(x_75, x_65);
x_81 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_72);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_74);
lean_ctor_set(x_81, 4, x_80);
lean_ctor_set(x_81, 5, x_76);
lean_ctor_set(x_81, 6, x_77);
lean_ctor_set(x_81, 7, x_78);
lean_ctor_set(x_81, 8, x_79);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
block_102:
{
uint8_t x_94; 
x_94 = l_Array_isEmpty___redArg(x_84);
lean_dec_ref(x_84);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec_ref(x_85);
lean_dec_ref(x_1);
x_95 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1;
x_96 = l_Lean_indentExpr(x_86);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_97, x_87, x_88, x_89, x_90, x_91, x_92);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
x_65 = x_85;
x_66 = lean_box(0);
goto block_83;
}
}
block_240:
{
uint8_t x_115; 
x_115 = l_Lean_Expr_isForall(x_107);
if (x_115 == 0)
{
lean_dec(x_105);
lean_dec_ref(x_104);
if (lean_obj_tag(x_3) == 0)
{
x_84 = x_103;
x_85 = x_106;
x_86 = x_107;
x_87 = x_108;
x_88 = x_109;
x_89 = x_110;
x_90 = x_111;
x_91 = x_112;
x_92 = x_113;
x_93 = lean_box(0);
goto block_102;
}
else
{
lean_dec_ref(x_3);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec_ref(x_106);
lean_dec_ref(x_103);
lean_dec_ref(x_1);
x_116 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3;
x_117 = l_Lean_indentExpr(x_107);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_118, x_108, x_109, x_110, x_111, x_112, x_113);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
return x_119;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
x_84 = x_103;
x_85 = x_106;
x_86 = x_107;
x_87 = x_108;
x_88 = x_109;
x_89 = x_110;
x_90 = x_111;
x_91 = x_112;
x_92 = x_113;
x_93 = lean_box(0);
goto block_102;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_103);
lean_dec(x_3);
x_123 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_123);
if (lean_obj_tag(x_105) == 2)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_1);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_ctor_get(x_1, 0);
x_126 = lean_ctor_get(x_1, 1);
x_127 = lean_ctor_get(x_1, 3);
x_128 = lean_ctor_get(x_1, 4);
x_129 = lean_ctor_get(x_1, 5);
x_130 = lean_ctor_get(x_1, 6);
x_131 = lean_ctor_get(x_1, 7);
x_132 = lean_ctor_get(x_1, 8);
x_133 = lean_ctor_get(x_1, 2);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_105);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_123, 2);
x_136 = lean_ctor_get_uint8(x_105, 0);
x_137 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_110, x_111, x_112, x_113);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec_ref(x_137);
lean_ctor_set_tag(x_105, 0);
lean_inc_ref(x_104);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc(x_111);
lean_inc_ref(x_110);
lean_inc(x_135);
x_138 = lean_apply_7(x_104, x_105, x_135, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_140, 0, x_136);
lean_inc(x_135);
x_141 = lean_apply_7(x_104, x_140, x_135, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = l_Lean_PersistentArray_push___redArg(x_123, x_139);
x_145 = l_Lean_PersistentArray_push___redArg(x_144, x_143);
lean_ctor_set(x_1, 2, x_145);
lean_ctor_set(x_141, 0, x_1);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
lean_dec(x_141);
x_147 = l_Lean_PersistentArray_push___redArg(x_123, x_139);
x_148 = l_Lean_PersistentArray_push___redArg(x_147, x_146);
lean_ctor_set(x_1, 2, x_148);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_1);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_139);
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
x_150 = !lean_is_exclusive(x_141);
if (x_150 == 0)
{
return x_141;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
lean_dec(x_141);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_153 = !lean_is_exclusive(x_138);
if (x_153 == 0)
{
return x_138;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_138, 0);
lean_inc(x_154);
lean_dec(x_138);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_free_object(x_105);
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_156 = !lean_is_exclusive(x_137);
if (x_156 == 0)
{
return x_137;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_137, 0);
lean_inc(x_157);
lean_dec(x_137);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_123, 2);
x_160 = lean_ctor_get_uint8(x_105, 0);
lean_dec(x_105);
x_161 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_110, x_111, x_112, x_113);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_161);
x_162 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_162, 0, x_160);
lean_inc_ref(x_104);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc(x_111);
lean_inc_ref(x_110);
lean_inc(x_159);
x_163 = lean_apply_7(x_104, x_162, x_159, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_165, 0, x_160);
lean_inc(x_159);
x_166 = lean_apply_7(x_104, x_165, x_159, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = l_Lean_PersistentArray_push___redArg(x_123, x_164);
x_170 = l_Lean_PersistentArray_push___redArg(x_169, x_167);
lean_ctor_set(x_1, 2, x_170);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 1, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_164);
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_175 = lean_ctor_get(x_163, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_176 = x_163;
} else {
 lean_dec_ref(x_163);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_free_object(x_1);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_178 = lean_ctor_get(x_161, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_179 = x_161;
} else {
 lean_dec_ref(x_161);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_1, 0);
x_182 = lean_ctor_get(x_1, 1);
x_183 = lean_ctor_get(x_1, 3);
x_184 = lean_ctor_get(x_1, 4);
x_185 = lean_ctor_get(x_1, 5);
x_186 = lean_ctor_get(x_1, 6);
x_187 = lean_ctor_get(x_1, 7);
x_188 = lean_ctor_get(x_1, 8);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_1);
x_189 = lean_ctor_get(x_123, 2);
x_190 = lean_ctor_get_uint8(x_105, 0);
if (lean_is_exclusive(x_105)) {
 x_191 = x_105;
} else {
 lean_dec_ref(x_105);
 x_191 = lean_box(0);
}
x_192 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_110, x_111, x_112, x_113);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_192);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 0, 1);
} else {
 x_193 = x_191;
 lean_ctor_set_tag(x_193, 0);
}
lean_ctor_set_uint8(x_193, 0, x_190);
lean_inc_ref(x_104);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc(x_111);
lean_inc_ref(x_110);
lean_inc(x_189);
x_194 = lean_apply_7(x_104, x_193, x_189, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_196, 0, x_190);
lean_inc(x_189);
x_197 = lean_apply_7(x_104, x_196, x_189, x_110, x_111, x_112, x_113, lean_box(0));
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = l_Lean_PersistentArray_push___redArg(x_123, x_195);
x_201 = l_Lean_PersistentArray_push___redArg(x_200, x_198);
x_202 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_202, 0, x_181);
lean_ctor_set(x_202, 1, x_182);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_183);
lean_ctor_set(x_202, 4, x_184);
lean_ctor_set(x_202, 5, x_185);
lean_ctor_set(x_202, 6, x_186);
lean_ctor_set(x_202, 7, x_187);
lean_ctor_set(x_202, 8, x_188);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(0, 1, 0);
} else {
 x_203 = x_199;
}
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_195);
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_123);
x_204 = lean_ctor_get(x_197, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_205 = x_197;
} else {
 lean_dec_ref(x_197);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_207 = lean_ctor_get(x_194, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_208 = x_194;
} else {
 lean_dec_ref(x_194);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_191);
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_123);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_104);
x_210 = lean_ctor_get(x_192, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_211 = x_192;
} else {
 lean_dec_ref(x_192);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_210);
return x_212;
}
}
}
else
{
switch (lean_obj_tag(x_105)) {
case 0:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_213 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_1, 8);
lean_inc(x_220);
lean_dec_ref(x_1);
x_221 = lean_ctor_get(x_123, 2);
lean_inc(x_221);
x_43 = x_110;
x_44 = x_218;
x_45 = x_220;
x_46 = x_217;
x_47 = x_216;
x_48 = x_123;
x_49 = x_105;
x_50 = x_111;
x_51 = x_112;
x_52 = x_215;
x_53 = lean_box(0);
x_54 = x_219;
x_55 = x_221;
x_56 = x_104;
x_57 = x_214;
x_58 = x_113;
x_59 = x_213;
goto block_64;
}
case 1:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_222 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_1, 8);
lean_inc(x_229);
lean_dec_ref(x_1);
x_230 = lean_ctor_get(x_123, 2);
lean_inc(x_230);
x_43 = x_110;
x_44 = x_227;
x_45 = x_229;
x_46 = x_226;
x_47 = x_225;
x_48 = x_123;
x_49 = x_105;
x_50 = x_111;
x_51 = x_112;
x_52 = x_224;
x_53 = lean_box(0);
x_54 = x_228;
x_55 = x_230;
x_56 = x_104;
x_57 = x_223;
x_58 = x_113;
x_59 = x_222;
goto block_64;
}
default: 
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_231 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_232);
x_233 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_233);
x_234 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_1, 8);
lean_inc(x_238);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_123, 2);
lean_inc(x_239);
x_13 = x_237;
x_14 = x_236;
x_15 = x_238;
x_16 = x_235;
x_17 = x_239;
x_18 = x_104;
x_19 = x_234;
x_20 = x_232;
x_21 = x_123;
x_22 = x_105;
x_23 = x_231;
x_24 = x_233;
x_25 = x_110;
x_26 = x_111;
x_27 = x_112;
x_28 = x_113;
x_29 = lean_box(0);
goto block_42;
}
}
}
}
}
block_305:
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_box(0);
x_250 = 1;
x_251 = lean_box(x_250);
lean_inc(x_2);
x_252 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(x_252, 0, x_2);
lean_closure_set(x_252, 1, x_4);
lean_closure_set(x_252, 2, x_249);
lean_closure_set(x_252, 3, x_251);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_243);
lean_inc_ref(x_242);
x_253 = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(x_252, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_253) == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_253, 0);
if (lean_obj_tag(x_255) == 1)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_free_object(x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_258);
x_259 = lean_infer_type(x_258, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_260);
x_261 = l_Lean_Meta_isProp(x_260, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_box(x_250);
x_264 = lean_box(x_5);
lean_inc(x_258);
lean_inc(x_257);
lean_inc_ref(x_1);
x_265 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(x_265, 0, x_1);
lean_closure_set(x_265, 1, x_2);
lean_closure_set(x_265, 2, x_257);
lean_closure_set(x_265, 3, x_258);
lean_closure_set(x_265, 4, x_263);
lean_closure_set(x_265, 5, x_264);
x_266 = lean_unbox(x_262);
lean_dec(x_262);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec_ref(x_265);
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_241);
lean_dec(x_3);
lean_dec_ref(x_1);
x_267 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5;
x_268 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_267, x_242, x_243, x_244, x_245, x_246, x_247);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
return x_268;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
else
{
x_103 = x_257;
x_104 = x_265;
x_105 = x_241;
x_106 = x_258;
x_107 = x_260;
x_108 = x_242;
x_109 = x_243;
x_110 = x_244;
x_111 = x_245;
x_112 = x_246;
x_113 = x_247;
x_114 = lean_box(0);
goto block_240;
}
}
else
{
uint8_t x_272; 
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_272 = !lean_is_exclusive(x_261);
if (x_272 == 0)
{
return x_261;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_261, 0);
lean_inc(x_273);
lean_dec(x_261);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_275 = !lean_is_exclusive(x_259);
if (x_275 == 0)
{
return x_259;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_259, 0);
lean_inc(x_276);
lean_dec(x_259);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
lean_dec(x_255);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_253, 0, x_1);
return x_253;
}
}
else
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_253, 0);
lean_inc(x_278);
lean_dec(x_253);
if (lean_obj_tag(x_278) == 1)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_281);
x_282 = lean_infer_type(x_281, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_283);
x_284 = l_Lean_Meta_isProp(x_283, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
x_286 = lean_box(x_250);
x_287 = lean_box(x_5);
lean_inc(x_281);
lean_inc(x_280);
lean_inc_ref(x_1);
x_288 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(x_288, 0, x_1);
lean_closure_set(x_288, 1, x_2);
lean_closure_set(x_288, 2, x_280);
lean_closure_set(x_288, 3, x_281);
lean_closure_set(x_288, 4, x_286);
lean_closure_set(x_288, 5, x_287);
x_289 = lean_unbox(x_285);
lean_dec(x_285);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec_ref(x_288);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_241);
lean_dec(x_3);
lean_dec_ref(x_1);
x_290 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5;
x_291 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_290, x_242, x_243, x_244, x_245, x_246, x_247);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
else
{
x_103 = x_280;
x_104 = x_288;
x_105 = x_241;
x_106 = x_281;
x_107 = x_283;
x_108 = x_242;
x_109 = x_243;
x_110 = x_244;
x_111 = x_245;
x_112 = x_246;
x_113 = x_247;
x_114 = lean_box(0);
goto block_240;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_284, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_296 = x_284;
} else {
 lean_dec_ref(x_284);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_282, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_299 = x_282;
} else {
 lean_dec_ref(x_282);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_298);
return x_300;
}
}
else
{
lean_object* x_301; 
lean_dec(x_278);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_1);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_302 = !lean_is_exclusive(x_253);
if (x_302 == 0)
{
return x_253;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_253, 0);
lean_inc(x_303);
lean_dec(x_253);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
block_314:
{
lean_object* x_313; 
x_313 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
x_241 = x_313;
x_242 = x_306;
x_243 = x_307;
x_244 = x_308;
x_245 = x_309;
x_246 = x_310;
x_247 = x_311;
x_248 = lean_box(0);
goto block_305;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_get(x_9);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
x_19 = l_Lean_ScopedEnvExtension_getState___redArg(x_18, x_2, x_14, x_17);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_23 = lean_array_push(x_16, x_19);
lean_ctor_set(x_1, 1, x_23);
x_24 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_26 = lean_array_push(x_16, x_19);
lean_ctor_set(x_1, 1, x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get(x_1, 3);
x_34 = lean_ctor_get(x_1, 4);
x_35 = lean_ctor_get(x_1, 5);
x_36 = lean_ctor_get(x_1, 6);
x_37 = lean_ctor_get(x_1, 7);
x_38 = lean_ctor_get(x_1, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_39 = lean_ctor_get(x_13, 2);
x_40 = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
x_41 = l_Lean_ScopedEnvExtension_getState___redArg(x_40, x_2, x_14, x_39);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = lean_array_push(x_31, x_41);
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set(x_44, 3, x_33);
lean_ctor_set(x_44, 4, x_34);
lean_ctor_set(x_44, 5, x_35);
lean_ctor_set(x_44, 6, x_36);
lean_ctor_set(x_44, 7, x_37);
lean_ctor_set(x_44, 8, x_38);
x_45 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_42;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 2);
x_17 = lean_ctor_get(x_8, 3);
x_18 = lean_ctor_get(x_8, 4);
x_19 = lean_ctor_get(x_8, 5);
x_20 = lean_ctor_get(x_8, 6);
x_21 = lean_ctor_get(x_8, 7);
x_22 = lean_ctor_get(x_8, 8);
x_23 = lean_ctor_get(x_8, 9);
x_24 = lean_ctor_get(x_8, 10);
x_25 = lean_ctor_get(x_8, 11);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_27 = lean_ctor_get(x_8, 12);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_8, 13);
x_30 = 0;
x_31 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
x_32 = l_Lean_replaceRef(x_1, x_19);
lean_inc_ref(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_33 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_16);
lean_ctor_set(x_33, 3, x_17);
lean_ctor_set(x_33, 4, x_18);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_20);
lean_ctor_set(x_33, 7, x_21);
lean_ctor_set(x_33, 8, x_22);
lean_ctor_set(x_33, 9, x_23);
lean_ctor_set(x_33, 10, x_24);
lean_ctor_set(x_33, 11, x_25);
lean_ctor_set(x_33, 12, x_27);
lean_ctor_set(x_33, 13, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*14 + 1, x_28);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_addEMatchTheorem(x_5, x_2, x_12, x_31, x_3, x_30, x_30, x_6, x_7, x_33, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_4 = x_13;
x_5 = x_35;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_6, 6);
x_9 = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(x_8, x_1);
if (x_9 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 6);
x_15 = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(x_14, x_1);
if (x_15 == 0)
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_7, 13);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set(x_31, 7, x_21);
lean_ctor_set(x_31, 8, x_22);
lean_ctor_set(x_31, 9, x_23);
lean_ctor_set(x_31, 10, x_24);
lean_ctor_set(x_31, 11, x_25);
lean_ctor_set(x_31, 12, x_27);
lean_ctor_set(x_31, 13, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_28);
x_32 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_8);
lean_dec_ref(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 2);
x_17 = lean_ctor_get(x_8, 3);
x_18 = lean_ctor_get(x_8, 4);
x_19 = lean_ctor_get(x_8, 5);
x_20 = lean_ctor_get(x_8, 6);
x_21 = lean_ctor_get(x_8, 7);
x_22 = lean_ctor_get(x_8, 8);
x_23 = lean_ctor_get(x_8, 9);
x_24 = lean_ctor_get(x_8, 10);
x_25 = lean_ctor_get(x_8, 11);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_27 = lean_ctor_get(x_8, 12);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_8, 13);
x_30 = 0;
x_31 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
x_32 = 1;
x_33 = l_Lean_replaceRef(x_1, x_19);
lean_inc_ref(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_34 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_15);
lean_ctor_set(x_34, 2, x_16);
lean_ctor_set(x_34, 3, x_17);
lean_ctor_set(x_34, 4, x_18);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_20);
lean_ctor_set(x_34, 7, x_21);
lean_ctor_set(x_34, 8, x_22);
lean_ctor_set(x_34, 9, x_23);
lean_ctor_set(x_34, 10, x_24);
lean_ctor_set(x_34, 11, x_25);
lean_ctor_set(x_34, 12, x_27);
lean_ctor_set(x_34, 13, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*14 + 1, x_28);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_2);
x_35 = l_Lean_Elab_Tactic_addEMatchTheorem(x_5, x_2, x_12, x_31, x_3, x_30, x_32, x_6, x_7, x_34, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_4 = x_13;
x_5 = x_36;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_10);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_14);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_13);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_12);
lean_ctor_set(x_43, 3, x_10);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_14);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_56);
x_62 = l_Lean_FileMap_toPosition(x_56, x_52);
lean_dec(x_52);
x_63 = l_Lean_FileMap_toPosition(x_56, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (x_51 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_65;
x_11 = x_53;
x_12 = x_64;
x_13 = x_61;
x_14 = x_54;
x_15 = x_55;
x_16 = x_62;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_65;
x_11 = x_53;
x_12 = x_64;
x_13 = x_61;
x_14 = x_54;
x_15 = x_55;
x_16 = x_62;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_56);
x_69 = l_Lean_FileMap_toPosition(x_56, x_52);
lean_dec(x_52);
x_70 = l_Lean_FileMap_toPosition(x_56, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (x_51 == 0)
{
lean_dec_ref(x_50);
x_10 = x_72;
x_11 = x_53;
x_12 = x_71;
x_13 = x_68;
x_14 = x_54;
x_15 = x_55;
x_16 = x_69;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_55);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_72;
x_11 = x_53;
x_12 = x_71;
x_13 = x_68;
x_14 = x_54;
x_15 = x_55;
x_16 = x_69;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_78, x_80);
lean_dec(x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_79;
x_52 = x_84;
x_53 = x_80;
x_54 = x_81;
x_55 = x_83;
x_56 = x_82;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_79;
x_52 = x_84;
x_53 = x_80;
x_54 = x_81;
x_55 = x_83;
x_56 = x_82;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_90);
lean_dec(x_90);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_95;
x_79 = x_89;
x_80 = x_91;
x_81 = x_94;
x_82 = x_93;
x_83 = x_92;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_95;
x_79 = x_89;
x_80 = x_91;
x_81 = x_94;
x_82 = x_93;
x_83 = x_92;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_102;
x_89 = x_101;
x_90 = x_103;
x_91 = x_106;
x_92 = x_105;
x_93 = x_104;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_102;
x_89 = x_101;
x_90 = x_103;
x_91 = x_106;
x_92 = x_105;
x_93 = x_104;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc_ref(x_110);
lean_inc_ref(x_111);
lean_inc(x_113);
x_101 = x_114;
x_102 = x_117;
x_103 = x_113;
x_104 = x_111;
x_105 = x_110;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_warningAsError;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_112, x_120);
lean_inc_ref(x_110);
lean_inc_ref(x_111);
lean_inc(x_113);
x_101 = x_114;
x_102 = x_117;
x_103 = x_113;
x_104 = x_111;
x_105 = x_110;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(x_11, x_1, x_2, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = 0;
x_11 = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_ResolveName_backward_privateInPublic_warn;
x_12 = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(x_11, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_18 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
lean_dec_ref(x_10);
if (x_18 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec(x_1);
goto block_17;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_isPrivateName(x_1);
if (x_19 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec(x_1);
goto block_17;
}
else
{
uint8_t x_20; 
x_20 = lean_unbox(x_13);
lean_dec(x_13);
if (x_20 == 0)
{
lean_dec_ref(x_6);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_21 = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1;
x_22 = 0;
x_23 = l_Lean_MessageData_ofConstName(x_1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_isPrivateName(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 6);
x_14 = lean_ctor_get(x_7, 7);
x_15 = lean_st_ref_get(x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_11, x_12, x_13, x_14, x_1);
if (x_2 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
lean_dec_ref(x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*8);
lean_dec_ref(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_7);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = ((lean_object*)(l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0));
lean_inc(x_17);
x_22 = l_List_find_x3f___redArg(x_21, x_17);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(x_24, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_17);
return x_25;
}
else
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_17);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_17);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_22);
lean_dec_ref(x_7);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_17);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_List_isEmpty___redArg(x_7);
if (x_8 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
x_14 = l_List_isEmpty___redArg(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_3);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
if (x_5 == 0)
{
x_30 = x_5;
goto block_59;
}
else
{
uint8_t x_60; 
x_60 = l_List_isEmpty___redArg(x_4);
if (x_60 == 0)
{
x_30 = x_5;
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = 0;
x_30 = x_61;
goto block_59;
}
}
block_25:
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_4);
x_3 = x_14;
x_4 = x_23;
x_5 = x_15;
x_6 = x_16;
x_7 = x_17;
x_8 = x_18;
x_9 = x_19;
x_10 = x_20;
x_11 = x_21;
goto _start;
}
block_59:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_30);
lean_inc_ref(x_2);
lean_inc_ref(x_29);
x_32 = lean_apply_2(x_2, x_29, x_31);
if (lean_obj_tag(x_32) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
if (x_5 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_3);
x_35 = l_Lean_MacroScopesView_review(x_29);
lean_inc_ref(x_10);
x_36 = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_box(0);
x_39 = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(x_37, x_38);
x_40 = l_List_isEmpty___redArg(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 1;
x_13 = x_34;
x_14 = x_33;
x_15 = x_41;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_25;
}
else
{
x_13 = x_34;
x_14 = x_33;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_25;
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_29);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_46);
lean_dec_ref(x_3);
x_13 = x_46;
x_14 = x_45;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_25;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_29);
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_29);
lean_dec_ref(x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_32, 0);
x_51 = l_Lean_LocalDecl_toExpr(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
lean_ctor_set(x_32, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_32);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_32, 0);
lean_inc(x_54);
lean_dec(x_32);
x_55 = l_Lean_LocalDecl_toExpr(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_13 = lean_array_fget_borrowed(x_3, x_9);
if (lean_obj_tag(x_13) == 0)
{
x_10 = x_13;
goto block_12;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = l_Lean_LocalDecl_isAuxDecl(x_14);
if (x_15 == 0)
{
lean_inc(x_1);
x_10 = x_1;
goto block_12;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_LocalDecl_userName(x_14);
x_17 = lean_name_eq(x_16, x_2);
lean_dec(x_16);
if (x_17 == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_inc_ref(x_13);
x_10 = x_13;
goto block_12;
}
}
}
block_12:
{
if (lean_obj_tag(x_10) == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_array_fget_borrowed(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(x_1, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_array_get_size(x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(x_1, x_2, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_1);
x_7 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(x_1, x_2, x_4);
return x_8;
}
else
{
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_LocalDecl_userName(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 1)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_16 = lean_array_fget_borrowed(x_6, x_12);
if (lean_obj_tag(x_16) == 0)
{
x_13 = x_16;
goto block_15;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
x_18 = l_Lean_LocalDecl_isAuxDecl(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc(x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(x_17, x_1);
x_13 = x_19;
goto block_15;
}
else
{
if (x_2 == 0)
{
if (x_18 == 0)
{
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_LocalDecl_fvarId(x_17);
x_22 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(x_3, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_51; lean_object* x_52; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_extractMacroScopes(x_23);
x_51 = lean_ctor_get(x_24, 0);
lean_inc(x_51);
lean_inc(x_51);
x_52 = lean_private_to_user_name(x_51);
if (lean_obj_tag(x_52) == 0)
{
x_25 = x_51;
goto block_50;
}
else
{
lean_object* x_53; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_25 = x_53;
goto block_50;
}
block_50:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_25);
lean_inc_ref(x_24);
x_28 = l_Lean_MacroScopesView_review(x_24);
x_29 = l_Lean_Name_isPrefixOf(x_4, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_24);
lean_inc(x_4);
lean_inc_ref(x_5);
lean_inc(x_17);
x_30 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(x_17, x_5, x_28, x_4);
lean_dec(x_28);
x_13 = x_30;
goto block_15;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_28);
x_31 = l_Lean_LocalDecl_userName(x_17);
x_32 = l_Lean_extractMacroScopes(x_31);
x_33 = l_Lean_MacroScopesView_isSuffixOf(x_32, x_5);
lean_dec_ref(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_24);
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_MacroScopesView_isSuffixOf(x_5, x_24);
lean_dec_ref(x_24);
if (x_35 == 0)
{
x_7 = x_12;
goto _start;
}
else
{
lean_inc_ref(x_16);
x_13 = x_16;
goto block_15;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
lean_inc_ref(x_40);
x_41 = l_Lean_MacroScopesView_review(x_40);
x_42 = l_Lean_Name_isPrefixOf(x_4, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_40);
lean_inc(x_4);
lean_inc_ref(x_5);
lean_inc(x_17);
x_43 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(x_17, x_5, x_41, x_4);
lean_dec(x_41);
x_13 = x_43;
goto block_15;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_41);
x_44 = l_Lean_LocalDecl_userName(x_17);
x_45 = l_Lean_extractMacroScopes(x_44);
x_46 = l_Lean_MacroScopesView_isSuffixOf(x_45, x_5);
lean_dec_ref(x_45);
if (x_46 == 0)
{
lean_dec_ref(x_40);
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_48; 
x_48 = l_Lean_MacroScopesView_isSuffixOf(x_5, x_40);
lean_dec_ref(x_40);
if (x_48 == 0)
{
x_7 = x_12;
goto _start;
}
else
{
lean_inc_ref(x_16);
x_13 = x_16;
goto block_15;
}
}
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_22);
lean_inc(x_17);
x_54 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(x_17, x_1);
x_13 = x_54;
goto block_15;
}
}
}
else
{
x_7 = x_12;
goto _start;
}
}
}
block_15:
{
if (lean_obj_tag(x_13) == 0)
{
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 1)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_array_fget_borrowed(x_6, x_12);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(x_1, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_array_get_size(x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_array_get_size(x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_array_get_size(x_8);
lean_inc_ref(x_5);
lean_inc(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(x_1, x_2, x_3, x_4, x_5, x_7);
return x_11;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
x_6 = l_Lean_MacroScopesView_review(x_4);
x_7 = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(x_6, x_5, x_1, x_2, x_4, x_3);
if (lean_obj_tag(x_7) == 0)
{
if (x_5 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(x_7, x_6, x_3);
lean_dec(x_6);
return x_8;
}
else
{
lean_dec(x_6);
return x_7;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(x_1, x_2, x_3, x_4, x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_9, 1);
x_11 = lean_ctor_get(x_9, 2);
x_12 = lean_ctor_get(x_6, 6);
x_13 = l_Lean_extractMacroScopes(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_inc_ref(x_10);
lean_inc(x_12);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_10);
x_16 = lean_box(0);
x_17 = 0;
x_18 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(x_13, x_15, x_14, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
x_9 = l_Lean_PersistentArray_push___redArg(x_8, x_5);
lean_ctor_set(x_2, 2, x_9);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get(x_2, 7);
x_19 = lean_ctor_get(x_2, 8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_20 = l_Lean_PersistentArray_push___redArg(x_13, x_5);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_16);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set(x_21, 7, x_18);
lean_ctor_set(x_21, 8, x_19);
x_1 = x_6;
x_2 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_173; lean_object* x_174; lean_object* x_477; lean_object* x_487; lean_object* x_488; 
x_487 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_4);
x_488 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_4, x_487, x_12, x_13);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
lean_dec_ref(x_488);
x_173 = x_489;
x_174 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_490; lean_object* x_491; uint8_t x_492; uint8_t x_561; 
x_490 = lean_ctor_get(x_488, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
x_561 = l_Lean_Exception_isInterrupt(x_490);
if (x_561 == 0)
{
uint8_t x_562; 
lean_inc(x_490);
x_562 = l_Lean_Exception_isRuntime(x_490);
x_492 = x_562;
goto block_560;
}
else
{
x_492 = x_561;
goto block_560;
}
block_560:
{
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_491);
x_493 = l_Lean_TSyntax_getId(x_4);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_inc(x_493);
x_494 = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(x_493, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec_ref(x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; 
x_496 = l_Lean_Meta_Grind_getExtension_x3f(x_493);
if (lean_obj_tag(x_496) == 0)
{
uint8_t x_497; 
x_497 = !lean_is_exclusive(x_496);
if (x_497 == 0)
{
lean_object* x_498; 
x_498 = lean_ctor_get(x_496, 0);
if (lean_obj_tag(x_498) == 1)
{
lean_free_object(x_496);
lean_dec(x_490);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
lean_dec_ref(x_498);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_499 = lean_ctor_get(x_3, 0);
lean_inc(x_499);
lean_dec_ref(x_3);
x_500 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
x_501 = l_Lean_MessageData_ofName(x_493);
x_502 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
x_503 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_504 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_499, x_504, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_499);
x_506 = !lean_is_exclusive(x_505);
if (x_506 == 0)
{
return x_505;
}
else
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_508, 0, x_507);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_493);
x_509 = lean_ctor_get(x_498, 0);
lean_inc(x_509);
lean_dec_ref(x_498);
x_510 = lean_box(0);
lean_inc_ref(x_1);
x_511 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(x_1, x_509, x_510, x_8, x_9, x_10, x_11, x_12, x_13);
x_477 = x_511;
goto block_486;
}
}
else
{
lean_object* x_512; uint8_t x_513; 
lean_dec(x_498);
x_512 = l_Lean_Name_getPrefix(x_493);
lean_dec(x_493);
x_513 = l_Lean_Name_isAnonymous(x_512);
lean_dec(x_512);
if (x_513 == 0)
{
lean_object* x_514; 
lean_free_object(x_496);
lean_dec(x_490);
x_514 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_514;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_496, 1);
lean_ctor_set(x_496, 0, x_490);
return x_496;
}
}
}
else
{
lean_object* x_515; 
x_515 = lean_ctor_get(x_496, 0);
lean_inc(x_515);
lean_dec(x_496);
if (lean_obj_tag(x_515) == 1)
{
lean_dec(x_490);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec_ref(x_515);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_516 = lean_ctor_get(x_3, 0);
lean_inc(x_516);
lean_dec_ref(x_3);
x_517 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
x_518 = l_Lean_MessageData_ofName(x_493);
x_519 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
x_520 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
x_521 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
x_522 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_516, x_521, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_516);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 x_524 = x_522;
} else {
 lean_dec_ref(x_522);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_523);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_493);
x_526 = lean_ctor_get(x_515, 0);
lean_inc(x_526);
lean_dec_ref(x_515);
x_527 = lean_box(0);
lean_inc_ref(x_1);
x_528 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(x_1, x_526, x_527, x_8, x_9, x_10, x_11, x_12, x_13);
x_477 = x_528;
goto block_486;
}
}
else
{
lean_object* x_529; uint8_t x_530; 
lean_dec(x_515);
x_529 = l_Lean_Name_getPrefix(x_493);
lean_dec(x_493);
x_530 = l_Lean_Name_isAnonymous(x_529);
lean_dec(x_529);
if (x_530 == 0)
{
lean_object* x_531; 
lean_dec(x_490);
x_531 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_531;
}
else
{
lean_object* x_532; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_532 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_532, 0, x_490);
return x_532;
}
}
}
}
else
{
uint8_t x_533; 
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_533 = !lean_is_exclusive(x_496);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_534 = lean_ctor_get(x_496, 0);
x_535 = lean_ctor_get(x_12, 5);
lean_inc(x_535);
lean_dec_ref(x_12);
x_536 = lean_io_error_to_string(x_534);
x_537 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_538 = l_Lean_MessageData_ofFormat(x_537);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_535);
lean_ctor_set(x_539, 1, x_538);
lean_ctor_set(x_496, 0, x_539);
return x_496;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_540 = lean_ctor_get(x_496, 0);
lean_inc(x_540);
lean_dec(x_496);
x_541 = lean_ctor_get(x_12, 5);
lean_inc(x_541);
lean_dec_ref(x_12);
x_542 = lean_io_error_to_string(x_540);
x_543 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_544 = l_Lean_MessageData_ofFormat(x_543);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_541);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_546, 0, x_545);
return x_546;
}
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
lean_dec_ref(x_495);
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_547 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
lean_inc(x_4);
x_548 = l_Lean_MessageData_ofSyntax(x_4);
x_549 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
x_550 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
x_551 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
x_552 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_4, x_551, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_553 = !lean_is_exclusive(x_552);
if (x_553 == 0)
{
return x_552;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_555, 0, x_554);
return x_555;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_556 = !lean_is_exclusive(x_494);
if (x_556 == 0)
{
return x_494;
}
else
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_494, 0);
lean_inc(x_557);
lean_dec(x_494);
x_558 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_558, 0, x_557);
return x_558;
}
}
}
else
{
lean_object* x_559; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
if (lean_is_scalar(x_491)) {
 x_559 = lean_alloc_ctor(1, 1, 0);
} else {
 x_559 = x_491;
}
lean_ctor_set(x_559, 0, x_490);
return x_559;
}
}
}
block_73:
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec_ref(x_17);
x_24 = 0;
lean_inc(x_15);
x_25 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_15, x_24, x_21, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_27);
x_28 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(x_16, x_27, x_24);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
x_29 = l_Lean_Meta_isInductivePredicate_x3f(x_27, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(x_2, x_4, x_5, x_33, x_28, x_19, x_20, x_21, x_22);
lean_dec_ref(x_21);
lean_dec(x_2);
return x_34;
}
else
{
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_ctor_get(x_36, 4);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(x_2, x_4, x_5, x_37, x_28, x_19, x_20, x_21, x_22);
lean_dec_ref(x_21);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_4);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_28);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_21, 5);
x_45 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
x_46 = 1;
x_47 = l_Lean_replaceRef(x_2, x_44);
lean_dec(x_44);
lean_dec(x_2);
lean_ctor_set(x_21, 5, x_47);
x_48 = l_Lean_Elab_Tactic_addEMatchTheorem(x_16, x_4, x_15, x_45, x_5, x_46, x_46, x_19, x_20, x_21, x_22);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
x_51 = lean_ctor_get(x_21, 2);
x_52 = lean_ctor_get(x_21, 3);
x_53 = lean_ctor_get(x_21, 4);
x_54 = lean_ctor_get(x_21, 5);
x_55 = lean_ctor_get(x_21, 6);
x_56 = lean_ctor_get(x_21, 7);
x_57 = lean_ctor_get(x_21, 8);
x_58 = lean_ctor_get(x_21, 9);
x_59 = lean_ctor_get(x_21, 10);
x_60 = lean_ctor_get(x_21, 11);
x_61 = lean_ctor_get_uint8(x_21, sizeof(void*)*14);
x_62 = lean_ctor_get(x_21, 12);
x_63 = lean_ctor_get_uint8(x_21, sizeof(void*)*14 + 1);
x_64 = lean_ctor_get(x_21, 13);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_65 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
x_66 = 1;
x_67 = l_Lean_replaceRef(x_2, x_54);
lean_dec(x_54);
lean_dec(x_2);
x_68 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_50);
lean_ctor_set(x_68, 2, x_51);
lean_ctor_set(x_68, 3, x_52);
lean_ctor_set(x_68, 4, x_53);
lean_ctor_set(x_68, 5, x_67);
lean_ctor_set(x_68, 6, x_55);
lean_ctor_set(x_68, 7, x_56);
lean_ctor_set(x_68, 8, x_57);
lean_ctor_set(x_68, 9, x_58);
lean_ctor_set(x_68, 10, x_59);
lean_ctor_set(x_68, 11, x_60);
lean_ctor_set(x_68, 12, x_62);
lean_ctor_set(x_68, 13, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*14, x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*14 + 1, x_63);
x_69 = l_Lean_Elab_Tactic_addEMatchTheorem(x_16, x_4, x_15, x_65, x_5, x_66, x_66, x_19, x_20, x_68, x_22);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_25);
if (x_70 == 0)
{
return x_25;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_25, 0);
lean_inc(x_71);
lean_dec(x_25);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
block_110:
{
lean_object* x_84; 
x_84 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_79, x_80, x_81, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_84);
x_85 = l_Lean_Meta_Grind_grindExt;
x_86 = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(x_85, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
lean_inc(x_74);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_74);
x_89 = l_Lean_Meta_Grind_Theorems_find___redArg(x_87, x_88);
lean_dec_ref(x_88);
x_90 = lean_box(0);
x_91 = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(x_75, x_89, x_90);
lean_dec(x_75);
x_92 = l_List_isEmpty___redArg(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_2);
x_93 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(x_91, x_76);
return x_93;
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_91);
lean_dec_ref(x_76);
x_94 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1;
x_95 = 0;
x_96 = l_Lean_MessageData_ofConstName(x_74, x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_2, x_99, x_77, x_78, x_79, x_80, x_81, x_82);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_86);
if (x_104 == 0)
{
return x_86;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_86, 0);
lean_inc(x_105);
lean_dec(x_86);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_84);
if (x_107 == 0)
{
return x_84;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_84, 0);
lean_inc(x_108);
lean_dec(x_84);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
block_160:
{
lean_object* x_119; 
x_119 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_114, x_115, x_116, x_117);
lean_dec(x_115);
lean_dec_ref(x_114);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_dec_ref(x_119);
x_120 = !lean_is_exclusive(x_116);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 5);
x_122 = l_Lean_replaceRef(x_2, x_121);
lean_dec(x_121);
lean_dec(x_2);
lean_ctor_set(x_116, 5, x_122);
lean_inc(x_111);
x_123 = l_Lean_Meta_Grind_validateCasesAttr(x_111, x_112, x_116, x_117);
lean_dec(x_117);
lean_dec_ref(x_116);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 0);
lean_dec(x_125);
x_126 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(x_113, x_111, x_112);
lean_ctor_set(x_123, 0, x_126);
return x_123;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
x_127 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(x_113, x_111, x_112);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec_ref(x_113);
lean_dec(x_111);
x_129 = !lean_is_exclusive(x_123);
if (x_129 == 0)
{
return x_123;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
lean_dec(x_123);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_132 = lean_ctor_get(x_116, 0);
x_133 = lean_ctor_get(x_116, 1);
x_134 = lean_ctor_get(x_116, 2);
x_135 = lean_ctor_get(x_116, 3);
x_136 = lean_ctor_get(x_116, 4);
x_137 = lean_ctor_get(x_116, 5);
x_138 = lean_ctor_get(x_116, 6);
x_139 = lean_ctor_get(x_116, 7);
x_140 = lean_ctor_get(x_116, 8);
x_141 = lean_ctor_get(x_116, 9);
x_142 = lean_ctor_get(x_116, 10);
x_143 = lean_ctor_get(x_116, 11);
x_144 = lean_ctor_get_uint8(x_116, sizeof(void*)*14);
x_145 = lean_ctor_get(x_116, 12);
x_146 = lean_ctor_get_uint8(x_116, sizeof(void*)*14 + 1);
x_147 = lean_ctor_get(x_116, 13);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_116);
x_148 = l_Lean_replaceRef(x_2, x_137);
lean_dec(x_137);
lean_dec(x_2);
x_149 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_149, 0, x_132);
lean_ctor_set(x_149, 1, x_133);
lean_ctor_set(x_149, 2, x_134);
lean_ctor_set(x_149, 3, x_135);
lean_ctor_set(x_149, 4, x_136);
lean_ctor_set(x_149, 5, x_148);
lean_ctor_set(x_149, 6, x_138);
lean_ctor_set(x_149, 7, x_139);
lean_ctor_set(x_149, 8, x_140);
lean_ctor_set(x_149, 9, x_141);
lean_ctor_set(x_149, 10, x_142);
lean_ctor_set(x_149, 11, x_143);
lean_ctor_set(x_149, 12, x_145);
lean_ctor_set(x_149, 13, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*14, x_144);
lean_ctor_set_uint8(x_149, sizeof(void*)*14 + 1, x_146);
lean_inc(x_111);
x_150 = l_Lean_Meta_Grind_validateCasesAttr(x_111, x_112, x_149, x_117);
lean_dec(x_117);
lean_dec_ref(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_151 = x_150;
} else {
 lean_dec_ref(x_150);
 x_151 = lean_box(0);
}
x_152 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(x_113, x_111, x_112);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_113);
lean_dec(x_111);
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_113);
lean_dec(x_111);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_119);
if (x_157 == 0)
{
return x_119;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_119, 0);
lean_inc(x_158);
lean_dec(x_119);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
block_172:
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_164);
lean_dec_ref(x_163);
x_170 = lean_ctor_get(x_161, 4);
lean_inc(x_170);
lean_dec_ref(x_161);
x_171 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(x_2, x_4, x_5, x_170, x_162, x_165, x_166, x_167, x_168);
lean_dec_ref(x_167);
lean_dec(x_2);
return x_171;
}
block_476:
{
lean_object* x_175; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_173);
x_175 = l_Lean_Linter_checkDeprecated(x_173, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_175) == 0)
{
lean_dec_ref(x_175);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_3, 0);
lean_inc(x_176);
lean_dec_ref(x_3);
lean_inc_ref(x_12);
x_177 = l_Lean_Meta_Grind_getAttrKindCore(x_176, x_12, x_13);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_177, 0);
switch (lean_obj_tag(x_179)) {
case 0:
{
lean_object* x_180; 
lean_free_object(x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
if (lean_obj_tag(x_180) == 9)
{
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_181 = lean_ctor_get(x_12, 0);
x_182 = lean_ctor_get(x_12, 1);
x_183 = lean_ctor_get(x_12, 2);
x_184 = lean_ctor_get(x_12, 3);
x_185 = lean_ctor_get(x_12, 4);
x_186 = lean_ctor_get(x_12, 5);
x_187 = lean_ctor_get(x_12, 6);
x_188 = lean_ctor_get(x_12, 7);
x_189 = lean_ctor_get(x_12, 8);
x_190 = lean_ctor_get(x_12, 9);
x_191 = lean_ctor_get(x_12, 10);
x_192 = lean_ctor_get(x_12, 11);
x_193 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_194 = lean_ctor_get(x_12, 12);
x_195 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_196 = lean_ctor_get(x_12, 13);
x_197 = l_Lean_replaceRef(x_2, x_186);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_185);
lean_inc(x_184);
lean_inc_ref(x_183);
lean_inc_ref(x_182);
lean_inc_ref(x_181);
x_198 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_198, 0, x_181);
lean_ctor_set(x_198, 1, x_182);
lean_ctor_set(x_198, 2, x_183);
lean_ctor_set(x_198, 3, x_184);
lean_ctor_set(x_198, 4, x_185);
lean_ctor_set(x_198, 5, x_197);
lean_ctor_set(x_198, 6, x_187);
lean_ctor_set(x_198, 7, x_188);
lean_ctor_set(x_198, 8, x_189);
lean_ctor_set(x_198, 9, x_190);
lean_ctor_set(x_198, 10, x_191);
lean_ctor_set(x_198, 11, x_192);
lean_ctor_set(x_198, 12, x_194);
lean_ctor_set(x_198, 13, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*14, x_193);
lean_ctor_set_uint8(x_198, sizeof(void*)*14 + 1, x_195);
x_199 = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(x_198, x_13);
lean_dec_ref(x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_dec_ref(x_199);
x_74 = x_173;
x_75 = x_180;
x_76 = x_1;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = x_12;
x_82 = x_13;
x_83 = lean_box(0);
goto block_110;
}
else
{
uint8_t x_200; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
}
else
{
x_74 = x_173;
x_75 = x_180;
x_76 = x_1;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = x_12;
x_82 = x_13;
x_83 = lean_box(0);
goto block_110;
}
}
else
{
uint8_t x_203; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_203 = !lean_is_exclusive(x_12);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_12, 5);
x_205 = 0;
x_206 = 1;
x_207 = l_Lean_replaceRef(x_2, x_204);
lean_dec(x_204);
lean_dec(x_2);
lean_ctor_set(x_12, 5, x_207);
x_208 = l_Lean_Elab_Tactic_addEMatchTheorem(x_1, x_4, x_173, x_180, x_5, x_205, x_206, x_10, x_11, x_12, x_13);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; uint8_t x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_209 = lean_ctor_get(x_12, 0);
x_210 = lean_ctor_get(x_12, 1);
x_211 = lean_ctor_get(x_12, 2);
x_212 = lean_ctor_get(x_12, 3);
x_213 = lean_ctor_get(x_12, 4);
x_214 = lean_ctor_get(x_12, 5);
x_215 = lean_ctor_get(x_12, 6);
x_216 = lean_ctor_get(x_12, 7);
x_217 = lean_ctor_get(x_12, 8);
x_218 = lean_ctor_get(x_12, 9);
x_219 = lean_ctor_get(x_12, 10);
x_220 = lean_ctor_get(x_12, 11);
x_221 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_222 = lean_ctor_get(x_12, 12);
x_223 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_224 = lean_ctor_get(x_12, 13);
lean_inc(x_224);
lean_inc(x_222);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_12);
x_225 = 0;
x_226 = 1;
x_227 = l_Lean_replaceRef(x_2, x_214);
lean_dec(x_214);
lean_dec(x_2);
x_228 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_228, 0, x_209);
lean_ctor_set(x_228, 1, x_210);
lean_ctor_set(x_228, 2, x_211);
lean_ctor_set(x_228, 3, x_212);
lean_ctor_set(x_228, 4, x_213);
lean_ctor_set(x_228, 5, x_227);
lean_ctor_set(x_228, 6, x_215);
lean_ctor_set(x_228, 7, x_216);
lean_ctor_set(x_228, 8, x_217);
lean_ctor_set(x_228, 9, x_218);
lean_ctor_set(x_228, 10, x_219);
lean_ctor_set(x_228, 11, x_220);
lean_ctor_set(x_228, 12, x_222);
lean_ctor_set(x_228, 13, x_224);
lean_ctor_set_uint8(x_228, sizeof(void*)*14, x_221);
lean_ctor_set_uint8(x_228, sizeof(void*)*14 + 1, x_223);
x_229 = l_Lean_Elab_Tactic_addEMatchTheorem(x_1, x_4, x_173, x_180, x_5, x_225, x_226, x_10, x_11, x_228, x_13);
return x_229;
}
}
}
case 1:
{
lean_free_object(x_177);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_230; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_230 = lean_ctor_get_uint8(x_179, 0);
lean_dec_ref(x_179);
x_111 = x_173;
x_112 = x_230;
x_113 = x_1;
x_114 = x_10;
x_115 = x_11;
x_116 = x_12;
x_117 = x_13;
x_118 = lean_box(0);
goto block_160;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec_ref(x_179);
lean_dec(x_173);
lean_dec(x_2);
lean_dec_ref(x_1);
x_231 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
x_232 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_231, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
return x_232;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
}
}
case 2:
{
uint8_t x_236; lean_object* x_237; 
lean_free_object(x_177);
x_236 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_173);
x_237 = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(x_173, x_236, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
if (lean_obj_tag(x_238) == 1)
{
lean_dec(x_173);
if (x_7 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_161 = x_239;
x_162 = x_1;
x_163 = x_8;
x_164 = x_9;
x_165 = x_10;
x_166 = x_11;
x_167 = x_12;
x_168 = x_13;
x_169 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
lean_dec_ref(x_238);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_240 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
x_241 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_240, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
return x_241;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
lean_dec(x_238);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_245 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7;
x_246 = l_Lean_MessageData_ofConstName(x_173, x_236);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9;
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_249, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
return x_250;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_254 = !lean_is_exclusive(x_237);
if (x_254 == 0)
{
return x_237;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_237, 0);
lean_inc(x_255);
lean_dec(x_237);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
case 3:
{
lean_free_object(x_177);
x_15 = x_173;
x_16 = x_1;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = lean_box(0);
goto block_73;
}
case 4:
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
lean_free_object(x_177);
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_257 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11;
x_258 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_257, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
return x_258;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_260);
return x_261;
}
}
case 5:
{
lean_object* x_262; lean_object* x_263; 
lean_free_object(x_177);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_262 = lean_ctor_get(x_179, 0);
lean_inc(x_262);
lean_dec_ref(x_179);
x_263 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_263, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_1);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_1, 5);
x_268 = l_Lean_Meta_Grind_SymbolPriorities_insert(x_267, x_173, x_262);
lean_ctor_set(x_1, 5, x_268);
lean_ctor_set(x_263, 0, x_1);
return x_263;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_269 = lean_ctor_get(x_1, 0);
x_270 = lean_ctor_get(x_1, 1);
x_271 = lean_ctor_get(x_1, 2);
x_272 = lean_ctor_get(x_1, 3);
x_273 = lean_ctor_get(x_1, 4);
x_274 = lean_ctor_get(x_1, 5);
x_275 = lean_ctor_get(x_1, 6);
x_276 = lean_ctor_get(x_1, 7);
x_277 = lean_ctor_get(x_1, 8);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_1);
x_278 = l_Lean_Meta_Grind_SymbolPriorities_insert(x_274, x_173, x_262);
x_279 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_279, 0, x_269);
lean_ctor_set(x_279, 1, x_270);
lean_ctor_set(x_279, 2, x_271);
lean_ctor_set(x_279, 3, x_272);
lean_ctor_set(x_279, 4, x_273);
lean_ctor_set(x_279, 5, x_278);
lean_ctor_set(x_279, 6, x_275);
lean_ctor_set(x_279, 7, x_276);
lean_ctor_set(x_279, 8, x_277);
lean_ctor_set(x_263, 0, x_279);
return x_263;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_263);
x_280 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_281);
x_282 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_282);
x_283 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_283);
x_284 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_284);
x_285 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_285);
x_286 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_286);
x_287 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_287);
x_288 = lean_ctor_get(x_1, 8);
lean_inc(x_288);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_289 = x_1;
} else {
 lean_dec_ref(x_1);
 x_289 = lean_box(0);
}
x_290 = l_Lean_Meta_Grind_SymbolPriorities_insert(x_285, x_173, x_262);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 9, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_280);
lean_ctor_set(x_291, 1, x_281);
lean_ctor_set(x_291, 2, x_282);
lean_ctor_set(x_291, 3, x_283);
lean_ctor_set(x_291, 4, x_284);
lean_ctor_set(x_291, 5, x_290);
lean_ctor_set(x_291, 6, x_286);
lean_ctor_set(x_291, 7, x_287);
lean_ctor_set(x_291, 8, x_288);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
}
else
{
uint8_t x_293; 
lean_dec(x_262);
lean_dec(x_173);
lean_dec_ref(x_1);
x_293 = !lean_is_exclusive(x_263);
if (x_293 == 0)
{
return x_263;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_263, 0);
lean_inc(x_294);
lean_dec(x_263);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
return x_295;
}
}
}
case 6:
{
lean_object* x_296; 
lean_free_object(x_177);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_296 = l_Lean_Meta_Grind_mkInjectiveTheorem(x_173, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_296) == 0)
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
uint8_t x_298; 
x_298 = !lean_is_exclusive(x_1);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_296, 0);
x_300 = lean_ctor_get(x_1, 3);
x_301 = l_Lean_PersistentArray_push___redArg(x_300, x_299);
lean_ctor_set(x_1, 3, x_301);
lean_ctor_set(x_296, 0, x_1);
return x_296;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_302 = lean_ctor_get(x_296, 0);
x_303 = lean_ctor_get(x_1, 0);
x_304 = lean_ctor_get(x_1, 1);
x_305 = lean_ctor_get(x_1, 2);
x_306 = lean_ctor_get(x_1, 3);
x_307 = lean_ctor_get(x_1, 4);
x_308 = lean_ctor_get(x_1, 5);
x_309 = lean_ctor_get(x_1, 6);
x_310 = lean_ctor_get(x_1, 7);
x_311 = lean_ctor_get(x_1, 8);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_1);
x_312 = l_Lean_PersistentArray_push___redArg(x_306, x_302);
x_313 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_313, 0, x_303);
lean_ctor_set(x_313, 1, x_304);
lean_ctor_set(x_313, 2, x_305);
lean_ctor_set(x_313, 3, x_312);
lean_ctor_set(x_313, 4, x_307);
lean_ctor_set(x_313, 5, x_308);
lean_ctor_set(x_313, 6, x_309);
lean_ctor_set(x_313, 7, x_310);
lean_ctor_set(x_313, 8, x_311);
lean_ctor_set(x_296, 0, x_313);
return x_296;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_314 = lean_ctor_get(x_296, 0);
lean_inc(x_314);
lean_dec(x_296);
x_315 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_315);
x_316 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_317);
x_318 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_318);
x_319 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_319);
x_320 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_320);
x_321 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_321);
x_322 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_322);
x_323 = lean_ctor_get(x_1, 8);
lean_inc(x_323);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_324 = x_1;
} else {
 lean_dec_ref(x_1);
 x_324 = lean_box(0);
}
x_325 = l_Lean_PersistentArray_push___redArg(x_318, x_314);
if (lean_is_scalar(x_324)) {
 x_326 = lean_alloc_ctor(0, 9, 0);
} else {
 x_326 = x_324;
}
lean_ctor_set(x_326, 0, x_315);
lean_ctor_set(x_326, 1, x_316);
lean_ctor_set(x_326, 2, x_317);
lean_ctor_set(x_326, 3, x_325);
lean_ctor_set(x_326, 4, x_319);
lean_ctor_set(x_326, 5, x_320);
lean_ctor_set(x_326, 6, x_321);
lean_ctor_set(x_326, 7, x_322);
lean_ctor_set(x_326, 8, x_323);
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_326);
return x_327;
}
}
else
{
uint8_t x_328; 
lean_dec_ref(x_1);
x_328 = !lean_is_exclusive(x_296);
if (x_328 == 0)
{
return x_296;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_296, 0);
lean_inc(x_329);
lean_dec(x_296);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
}
case 7:
{
lean_object* x_331; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_331 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(x_1, x_173);
lean_ctor_set(x_177, 0, x_331);
return x_177;
}
case 8:
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; 
lean_free_object(x_177);
lean_dec_ref(x_179);
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_332 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13;
x_333 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_332, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
return x_333;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_335);
return x_336;
}
}
default: 
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_free_object(x_177);
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_337 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15;
x_338 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_337, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
return x_338;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
}
else
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_177, 0);
lean_inc(x_342);
lean_dec(x_177);
switch (lean_obj_tag(x_342)) {
case 0:
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
if (lean_obj_tag(x_343) == 9)
{
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_344 = lean_ctor_get(x_12, 0);
x_345 = lean_ctor_get(x_12, 1);
x_346 = lean_ctor_get(x_12, 2);
x_347 = lean_ctor_get(x_12, 3);
x_348 = lean_ctor_get(x_12, 4);
x_349 = lean_ctor_get(x_12, 5);
x_350 = lean_ctor_get(x_12, 6);
x_351 = lean_ctor_get(x_12, 7);
x_352 = lean_ctor_get(x_12, 8);
x_353 = lean_ctor_get(x_12, 9);
x_354 = lean_ctor_get(x_12, 10);
x_355 = lean_ctor_get(x_12, 11);
x_356 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_357 = lean_ctor_get(x_12, 12);
x_358 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_359 = lean_ctor_get(x_12, 13);
x_360 = l_Lean_replaceRef(x_2, x_349);
lean_inc_ref(x_359);
lean_inc(x_357);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_348);
lean_inc(x_347);
lean_inc_ref(x_346);
lean_inc_ref(x_345);
lean_inc_ref(x_344);
x_361 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_361, 0, x_344);
lean_ctor_set(x_361, 1, x_345);
lean_ctor_set(x_361, 2, x_346);
lean_ctor_set(x_361, 3, x_347);
lean_ctor_set(x_361, 4, x_348);
lean_ctor_set(x_361, 5, x_360);
lean_ctor_set(x_361, 6, x_350);
lean_ctor_set(x_361, 7, x_351);
lean_ctor_set(x_361, 8, x_352);
lean_ctor_set(x_361, 9, x_353);
lean_ctor_set(x_361, 10, x_354);
lean_ctor_set(x_361, 11, x_355);
lean_ctor_set(x_361, 12, x_357);
lean_ctor_set(x_361, 13, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*14, x_356);
lean_ctor_set_uint8(x_361, sizeof(void*)*14 + 1, x_358);
x_362 = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(x_361, x_13);
lean_dec_ref(x_361);
if (lean_obj_tag(x_362) == 0)
{
lean_dec_ref(x_362);
x_74 = x_173;
x_75 = x_343;
x_76 = x_1;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = x_12;
x_82 = x_13;
x_83 = lean_box(0);
goto block_110;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_363);
return x_365;
}
}
else
{
x_74 = x_173;
x_75 = x_343;
x_76 = x_1;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = x_12;
x_82 = x_13;
x_83 = lean_box(0);
goto block_110;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_366 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_366);
x_367 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_367);
x_368 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_368);
x_369 = lean_ctor_get(x_12, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_12, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_12, 5);
lean_inc(x_371);
x_372 = lean_ctor_get(x_12, 6);
lean_inc(x_372);
x_373 = lean_ctor_get(x_12, 7);
lean_inc(x_373);
x_374 = lean_ctor_get(x_12, 8);
lean_inc(x_374);
x_375 = lean_ctor_get(x_12, 9);
lean_inc(x_375);
x_376 = lean_ctor_get(x_12, 10);
lean_inc(x_376);
x_377 = lean_ctor_get(x_12, 11);
lean_inc(x_377);
x_378 = lean_ctor_get_uint8(x_12, sizeof(void*)*14);
x_379 = lean_ctor_get(x_12, 12);
lean_inc(x_379);
x_380 = lean_ctor_get_uint8(x_12, sizeof(void*)*14 + 1);
x_381 = lean_ctor_get(x_12, 13);
lean_inc_ref(x_381);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 lean_ctor_release(x_12, 9);
 lean_ctor_release(x_12, 10);
 lean_ctor_release(x_12, 11);
 lean_ctor_release(x_12, 12);
 lean_ctor_release(x_12, 13);
 x_382 = x_12;
} else {
 lean_dec_ref(x_12);
 x_382 = lean_box(0);
}
x_383 = 0;
x_384 = 1;
x_385 = l_Lean_replaceRef(x_2, x_371);
lean_dec(x_371);
lean_dec(x_2);
if (lean_is_scalar(x_382)) {
 x_386 = lean_alloc_ctor(0, 14, 2);
} else {
 x_386 = x_382;
}
lean_ctor_set(x_386, 0, x_366);
lean_ctor_set(x_386, 1, x_367);
lean_ctor_set(x_386, 2, x_368);
lean_ctor_set(x_386, 3, x_369);
lean_ctor_set(x_386, 4, x_370);
lean_ctor_set(x_386, 5, x_385);
lean_ctor_set(x_386, 6, x_372);
lean_ctor_set(x_386, 7, x_373);
lean_ctor_set(x_386, 8, x_374);
lean_ctor_set(x_386, 9, x_375);
lean_ctor_set(x_386, 10, x_376);
lean_ctor_set(x_386, 11, x_377);
lean_ctor_set(x_386, 12, x_379);
lean_ctor_set(x_386, 13, x_381);
lean_ctor_set_uint8(x_386, sizeof(void*)*14, x_378);
lean_ctor_set_uint8(x_386, sizeof(void*)*14 + 1, x_380);
x_387 = l_Lean_Elab_Tactic_addEMatchTheorem(x_1, x_4, x_173, x_343, x_5, x_383, x_384, x_10, x_11, x_386, x_13);
return x_387;
}
}
case 1:
{
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_388; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_388 = lean_ctor_get_uint8(x_342, 0);
lean_dec_ref(x_342);
x_111 = x_173;
x_112 = x_388;
x_113 = x_1;
x_114 = x_10;
x_115 = x_11;
x_116 = x_12;
x_117 = x_13;
x_118 = lean_box(0);
goto block_160;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec_ref(x_342);
lean_dec(x_173);
lean_dec(x_2);
lean_dec_ref(x_1);
x_389 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
x_390 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_389, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
case 2:
{
uint8_t x_394; lean_object* x_395; 
x_394 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_173);
x_395 = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(x_173, x_394, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec_ref(x_395);
if (lean_obj_tag(x_396) == 1)
{
lean_dec(x_173);
if (x_7 == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
x_161 = x_397;
x_162 = x_1;
x_163 = x_8;
x_164 = x_9;
x_165 = x_10;
x_166 = x_11;
x_167 = x_12;
x_168 = x_13;
x_169 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec_ref(x_396);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_398 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
x_399 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_398, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_401 = x_399;
} else {
 lean_dec_ref(x_399);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_396);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_403 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7;
x_404 = l_Lean_MessageData_ofConstName(x_173, x_394);
x_405 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
x_406 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9;
x_407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_407, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 1, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_412 = lean_ctor_get(x_395, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_413 = x_395;
} else {
 lean_dec_ref(x_395);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 1, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_412);
return x_414;
}
}
case 3:
{
x_15 = x_173;
x_16 = x_1;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = lean_box(0);
goto block_73;
}
case 4:
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_415 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11;
x_416 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_415, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
case 5:
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_420 = lean_ctor_get(x_342, 0);
lean_inc(x_420);
lean_dec_ref(x_342);
x_421 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(x_5, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 x_422 = x_421;
} else {
 lean_dec_ref(x_421);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_423);
x_424 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_424);
x_425 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_425);
x_426 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_426);
x_427 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_427);
x_428 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_428);
x_429 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_429);
x_430 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_430);
x_431 = lean_ctor_get(x_1, 8);
lean_inc(x_431);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_432 = x_1;
} else {
 lean_dec_ref(x_1);
 x_432 = lean_box(0);
}
x_433 = l_Lean_Meta_Grind_SymbolPriorities_insert(x_428, x_173, x_420);
if (lean_is_scalar(x_432)) {
 x_434 = lean_alloc_ctor(0, 9, 0);
} else {
 x_434 = x_432;
}
lean_ctor_set(x_434, 0, x_423);
lean_ctor_set(x_434, 1, x_424);
lean_ctor_set(x_434, 2, x_425);
lean_ctor_set(x_434, 3, x_426);
lean_ctor_set(x_434, 4, x_427);
lean_ctor_set(x_434, 5, x_433);
lean_ctor_set(x_434, 6, x_429);
lean_ctor_set(x_434, 7, x_430);
lean_ctor_set(x_434, 8, x_431);
if (lean_is_scalar(x_422)) {
 x_435 = lean_alloc_ctor(0, 1, 0);
} else {
 x_435 = x_422;
}
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_420);
lean_dec(x_173);
lean_dec_ref(x_1);
x_436 = lean_ctor_get(x_421, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
case 6:
{
lean_object* x_439; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_439 = l_Lean_Meta_Grind_mkInjectiveTheorem(x_173, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_442);
x_443 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_443);
x_444 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_444);
x_445 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_445);
x_446 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_446);
x_447 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_447);
x_448 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_448);
x_449 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_449);
x_450 = lean_ctor_get(x_1, 8);
lean_inc(x_450);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 x_451 = x_1;
} else {
 lean_dec_ref(x_1);
 x_451 = lean_box(0);
}
x_452 = l_Lean_PersistentArray_push___redArg(x_445, x_440);
if (lean_is_scalar(x_451)) {
 x_453 = lean_alloc_ctor(0, 9, 0);
} else {
 x_453 = x_451;
}
lean_ctor_set(x_453, 0, x_442);
lean_ctor_set(x_453, 1, x_443);
lean_ctor_set(x_453, 2, x_444);
lean_ctor_set(x_453, 3, x_452);
lean_ctor_set(x_453, 4, x_446);
lean_ctor_set(x_453, 5, x_447);
lean_ctor_set(x_453, 6, x_448);
lean_ctor_set(x_453, 7, x_449);
lean_ctor_set(x_453, 8, x_450);
if (lean_is_scalar(x_441)) {
 x_454 = lean_alloc_ctor(0, 1, 0);
} else {
 x_454 = x_441;
}
lean_ctor_set(x_454, 0, x_453);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec_ref(x_1);
x_455 = lean_ctor_get(x_439, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_456 = x_439;
} else {
 lean_dec_ref(x_439);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_455);
return x_457;
}
}
case 7:
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_458 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(x_1, x_173);
x_459 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_459, 0, x_458);
return x_459;
}
case 8:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec_ref(x_342);
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_460 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13;
x_461 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_460, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 1, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_462);
return x_464;
}
default: 
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_465 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15;
x_466 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_465, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 1, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_467);
return x_469;
}
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_470 = !lean_is_exclusive(x_177);
if (x_470 == 0)
{
return x_177;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_177, 0);
lean_inc(x_471);
lean_dec(x_177);
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_471);
return x_472;
}
}
}
else
{
lean_dec(x_3);
x_15 = x_173;
x_16 = x_1;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = lean_box(0);
goto block_73;
}
}
else
{
uint8_t x_473; 
lean_dec(x_173);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_473 = !lean_is_exclusive(x_175);
if (x_473 == 0)
{
return x_175;
}
else
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_175, 0);
lean_inc(x_474);
lean_dec(x_175);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_474);
return x_475;
}
}
}
block_486:
{
uint8_t x_478; 
x_478 = !lean_is_exclusive(x_477);
if (x_478 == 0)
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_477, 0);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
lean_free_object(x_477);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
lean_dec_ref(x_479);
x_173 = x_480;
x_174 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_481; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_481 = lean_ctor_get(x_479, 0);
lean_inc(x_481);
lean_dec_ref(x_479);
lean_ctor_set(x_477, 0, x_481);
return x_477;
}
}
else
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_477, 0);
lean_inc(x_482);
lean_dec(x_477);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_173 = x_483;
x_174 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec_ref(x_482);
x_485 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_485, 0, x_484);
return x_485;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = lean_unbox(x_7);
x_18 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(x_1, x_2, x_3, x_4, x_15, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(x_2, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(x_1, x_2, x_3, x_5, x_6, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
x_12 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_1, x_11, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_14 = l_Lean_Linter_checkDeprecated(x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; 
lean_dec_ref(x_14);
x_15 = 0;
lean_inc(x_13);
x_16 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_13, x_15, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_19);
x_20 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_19, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(x_2, x_19, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_inc(x_13);
x_36 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(x_2, x_13);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_16);
x_37 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(x_2, x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_49 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(x_2, x_13);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_16, 0, x_51);
return x_16;
}
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_16, 0);
lean_inc(x_52);
lean_dec(x_16);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_53);
x_54 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_53, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_dec_ref(x_54);
x_55 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(x_2, x_53, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_52);
lean_inc(x_13);
x_67 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(x_2, x_13);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(x_2, x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_77 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(x_2, x_13);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_81 = !lean_is_exclusive(x_16);
if (x_81 == 0)
{
return x_16;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_16, 0);
lean_inc(x_82);
lean_dec(x_16);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_84 = !lean_is_exclusive(x_14);
if (x_84 == 0)
{
return x_14;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
lean_dec(x_14);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_12);
if (x_87 == 0)
{
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_12, 0);
lean_inc(x_88);
lean_dec(x_12);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_19, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_TSyntax_getId(x_17);
lean_inc_ref(x_13);
lean_inc_ref(x_11);
x_33 = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(x_32, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_34, 0);
lean_inc(x_54);
lean_dec_ref(x_34);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 1)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_4, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_box(0);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 1, x_61);
lean_ctor_set(x_55, 0, x_62);
lean_ctor_set(x_59, 0, x_55);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 1, x_63);
lean_ctor_set(x_55, 0, x_64);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_55);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_55);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_55);
x_69 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_4, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
lean_dec(x_55);
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_12;
x_39 = x_13;
x_40 = x_14;
goto block_53;
}
}
else
{
lean_dec(x_34);
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_12;
x_39 = x_13;
x_40 = x_14;
goto block_53;
}
block_53:
{
lean_object* x_41; 
x_41 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(x_2, x_3, x_8, x_17, x_4, x_5, x_6, x_35, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_33, 0);
lean_inc(x_79);
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(x_1, x_2, x_3, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(x_2, x_1, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_4, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_TSyntax_getId(x_17);
lean_inc_ref(x_13);
lean_inc_ref(x_11);
x_33 = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(x_32, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_34, 0);
lean_inc(x_54);
lean_dec_ref(x_34);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 1)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_4, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_box(0);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 1, x_61);
lean_ctor_set(x_55, 0, x_62);
lean_ctor_set(x_59, 0, x_55);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 1, x_63);
lean_ctor_set(x_55, 0, x_64);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_55);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_55);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_55);
x_69 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(x_2, x_3, x_8, x_17, x_4, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
lean_dec(x_55);
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_12;
x_39 = x_13;
x_40 = x_14;
goto block_53;
}
}
else
{
lean_dec(x_34);
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_12;
x_39 = x_13;
x_40 = x_14;
goto block_53;
}
block_53:
{
lean_object* x_41; 
x_41 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(x_2, x_3, x_8, x_17, x_4, x_5, x_6, x_35, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_33, 0);
lean_inc(x_79);
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(x_1, x_2, x_3, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_19;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_27; lean_object* x_28; lean_object* x_32; uint8_t x_37; 
x_37 = lean_usize_dec_lt(x_6, x_5);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_7);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_array_uget(x_4, x_6);
x_40 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(x_39);
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_43 = l_Lean_MessageData_ofSyntax(x_39);
x_44 = l_Lean_indentD(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
lean_inc_ref(x_8);
x_46 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_45, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_27 = x_47;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Lean_Syntax_getArg(x_39, x_48);
x_50 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(x_49);
x_51 = l_Lean_Syntax_isOfKind(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(x_49);
x_53 = l_Lean_Syntax_isOfKind(x_49, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(x_49);
x_55 = l_Lean_Syntax_isOfKind(x_49, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(x_49);
x_57 = l_Lean_Syntax_isOfKind(x_49, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_49);
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_59 = l_Lean_MessageData_ofSyntax(x_39);
x_60 = l_Lean_indentD(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_inc_ref(x_8);
x_62 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_61, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_27 = x_63;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Syntax_getArg(x_49, x_64);
lean_dec(x_49);
x_66 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(x_65);
x_67 = l_Lean_Syntax_isOfKind(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_68 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_69 = l_Lean_MessageData_ofSyntax(x_39);
x_70 = l_Lean_indentD(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_inc_ref(x_8);
x_72 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_71, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_27 = x_73;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_dec(x_39);
if (x_2 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15;
lean_inc_ref(x_12);
lean_inc_ref(x_8);
x_75 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_65, x_74, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc_ref(x_7);
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(x_65, x_7, x_76, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_65);
x_32 = x_77;
goto block_36;
}
else
{
lean_object* x_78; 
lean_dec(x_65);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec_ref(x_75);
x_27 = x_78;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(0);
lean_inc_ref(x_7);
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(x_65, x_7, x_79, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_65);
x_32 = x_80;
goto block_36;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = l_Lean_Syntax_getArg(x_49, x_81);
x_83 = l_Lean_Syntax_isNone(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_inc(x_82);
x_84 = l_Lean_Syntax_matchesNull(x_82, x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_82);
lean_dec(x_49);
x_85 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_86 = l_Lean_MessageData_ofSyntax(x_39);
x_87 = l_Lean_indentD(x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
lean_inc_ref(x_8);
x_89 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_88, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_27 = x_90;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Syntax_getArg(x_82, x_48);
lean_dec(x_82);
x_92 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(x_91);
x_93 = l_Lean_Syntax_isOfKind(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_49);
x_94 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_95 = l_Lean_MessageData_ofSyntax(x_39);
x_96 = l_Lean_indentD(x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
lean_inc_ref(x_8);
x_98 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_97, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_27 = x_99;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_91);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_102 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(x_49, x_7, x_39, x_37, x_2, x_3, x_100, x_101, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_49);
x_32 = x_102;
goto block_36;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_82);
x_103 = lean_box(0);
x_104 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_105 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(x_49, x_7, x_39, x_37, x_2, x_3, x_103, x_104, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_49);
x_32 = x_105;
goto block_36;
}
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_Syntax_getArg(x_49, x_48);
x_107 = l_Lean_Syntax_isNone(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_unsigned_to_nat(1u);
lean_inc(x_106);
x_109 = l_Lean_Syntax_matchesNull(x_106, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_106);
lean_dec(x_49);
x_110 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_111 = l_Lean_MessageData_ofSyntax(x_39);
x_112 = l_Lean_indentD(x_111);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
lean_inc_ref(x_8);
x_114 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_113, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_114);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_27 = x_115;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = l_Lean_Syntax_getArg(x_106, x_48);
lean_dec(x_106);
x_117 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(x_116);
x_118 = l_Lean_Syntax_isOfKind(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_116);
lean_dec(x_49);
x_119 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_120 = l_Lean_MessageData_ofSyntax(x_39);
x_121 = l_Lean_indentD(x_120);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
lean_inc_ref(x_8);
x_123 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_122, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_123) == 0)
{
lean_dec_ref(x_123);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_27 = x_124;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_116);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_127 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(x_49, x_7, x_39, x_51, x_2, x_3, x_125, x_126, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_49);
x_32 = x_127;
goto block_36;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_106);
x_128 = lean_box(0);
x_129 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_130 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(x_49, x_7, x_39, x_51, x_2, x_3, x_128, x_129, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_49);
x_32 = x_130;
goto block_36;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_unsigned_to_nat(1u);
x_132 = l_Lean_Syntax_getArg(x_49, x_131);
lean_dec(x_49);
x_133 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(x_132);
x_134 = l_Lean_Syntax_isOfKind(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
x_135 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
x_136 = l_Lean_MessageData_ofSyntax(x_39);
x_137 = l_Lean_indentD(x_136);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
lean_inc_ref(x_8);
x_139 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(x_138, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_27 = x_140;
x_28 = lean_box(0);
goto block_31;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_39);
x_141 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_7);
x_142 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(x_132, x_7, x_141, x_8, x_9, x_10, x_11, x_12, x_13);
x_32 = x_142;
goto block_36;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17;
lean_inc_ref(x_12);
lean_inc_ref(x_8);
x_144 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(x_39, x_143, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_39);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_7);
x_146 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(x_132, x_7, x_145, x_8, x_9, x_10, x_11, x_12, x_13);
x_32 = x_146;
goto block_36;
}
else
{
lean_object* x_147; 
lean_dec(x_132);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec_ref(x_144);
x_27 = x_147;
x_28 = lean_box(0);
goto block_31;
}
}
}
}
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_6 = x_18;
x_7 = x_15;
goto _start;
}
block_26:
{
if (x_23 == 0)
{
if (x_1 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_dec_ref(x_21);
x_15 = x_7;
x_16 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
}
block_31:
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isInterrupt(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
lean_inc_ref(x_27);
x_30 = l_Lean_Exception_isRuntime(x_27);
x_21 = x_27;
x_22 = lean_box(0);
x_23 = x_30;
goto block_26;
}
else
{
x_21 = x_27;
x_22 = lean_box(0);
x_23 = x_29;
goto block_26;
}
}
block_36:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_7);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_15 = x_34;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_27 = x_35;
x_28 = lean_box(0);
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_unbox(x_1);
x_16 = lean_unbox(x_2);
x_17 = lean_unbox(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(x_15, x_16, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_array_size(x_2);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(x_4, x_3, x_5, x_2, x_13, x_14, x_1, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_Grind_isMatchEqLikeDeclName(x_13, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_18 = x_4;
} else {
 lean_dec_ref(x_4);
 x_18 = lean_box(0);
}
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_29 = lean_unbox(x_21);
lean_dec(x_21);
if (x_29 == 0)
{
lean_dec(x_19);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_PersistentArray_push___redArg(x_17, x_19);
x_23 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; 
if (lean_is_scalar(x_18)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_18;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_18 = x_4;
} else {
 lean_dec_ref(x_4);
 x_18 = lean_box(0);
}
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_29 = lean_unbox(x_21);
lean_dec(x_21);
if (x_29 == 0)
{
lean_dec(x_19);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_PersistentArray_push___redArg(x_17, x_19);
x_23 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
if (lean_is_scalar(x_18)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_18;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(x_1, x_2, x_26, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_18 = x_4;
} else {
 lean_dec_ref(x_4);
 x_18 = lean_box(0);
}
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_29 = lean_unbox(x_21);
lean_dec(x_21);
if (x_29 == 0)
{
lean_dec(x_19);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_PersistentArray_push___redArg(x_17, x_19);
x_23 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; 
if (lean_is_scalar(x_18)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_18;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_18 = x_4;
} else {
 lean_dec_ref(x_4);
 x_18 = lean_box(0);
}
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_29 = lean_unbox(x_21);
lean_dec(x_21);
if (x_29 == 0)
{
lean_dec(x_19);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_PersistentArray_push___redArg(x_17, x_19);
x_23 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
if (lean_is_scalar(x_18)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_18;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_26, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_array_size(x_15);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(x_1, x_15, x_18, x_19, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_24);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_25; 
lean_inc_ref(x_23);
lean_dec(x_22);
lean_free_object(x_2);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_2);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_27);
lean_dec(x_26);
lean_free_object(x_2);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_2);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
x_38 = lean_array_size(x_35);
x_39 = 0;
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(x_1, x_35, x_38, x_39, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_43);
lean_dec(x_41);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec_ref(x_43);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
x_56 = lean_array_size(x_53);
x_57 = 0;
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(x_53, x_56, x_57, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_53);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_60, 0);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_ctor_set(x_2, 0, x_62);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
else
{
lean_object* x_63; 
lean_inc_ref(x_61);
lean_dec(x_60);
lean_free_object(x_2);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec_ref(x_61);
lean_ctor_set(x_58, 0, x_63);
return x_58;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_64, 0);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_ctor_set(x_2, 0, x_66);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_2);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_65);
lean_dec(x_64);
lean_free_object(x_2);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec_ref(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_free_object(x_2);
x_70 = !lean_is_exclusive(x_58);
if (x_70 == 0)
{
return x_58;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
x_76 = lean_array_size(x_73);
x_77 = 0;
x_78 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(x_73, x_76, x_77, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_73);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_79, 0);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_inc_ref(x_81);
lean_dec(x_79);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec_ref(x_81);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_80;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_4, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_2, x_4);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_19);
x_22 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(x_1, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_22, 0, x_5);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_free_object(x_22);
lean_dec(x_19);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_box(0);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_5, 0, x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_19);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_box(0);
lean_ctor_set(x_5, 1, x_34);
lean_ctor_set(x_5, 0, x_35);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_5);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
x_43 = lean_array_uget(x_2, x_4);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_42);
x_44 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(x_1, x_43, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_46);
lean_dec(x_42);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec_ref(x_45);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = 1;
x_54 = lean_usize_add(x_4, x_53);
x_4 = x_54;
x_5 = x_52;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_15 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(x_2, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_15);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_size(x_14);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(x_14, x_22, x_23, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_14);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; 
lean_inc_ref(x_27);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_31);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec_ref(x_39);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_size(x_14);
x_46 = 0;
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(x_14, x_45, x_46, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_inc_ref(x_50);
lean_dec(x_48);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_56 = x_47;
} else {
 lean_dec_ref(x_47);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_58 = !lean_is_exclusive(x_15);
if (x_58 == 0)
{
return x_15;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_15, 0);
lean_inc(x_59);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0;
x_4 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2;
x_13 = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37, lean_object* x_38) {
_start:
{
lean_object* x_40; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
x_40 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(x_2, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0;
x_46 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_4);
lean_ctor_set(x_46, 5, x_5);
lean_ctor_set(x_46, 6, x_6);
lean_ctor_set(x_46, 7, x_7);
lean_ctor_set(x_46, 8, x_8);
lean_ctor_set(x_46, 9, x_9);
lean_ctor_set(x_46, 10, x_10);
x_47 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_13);
lean_ctor_set(x_47, 3, x_14);
lean_ctor_set(x_47, 4, x_15);
lean_ctor_set(x_47, 5, x_16);
lean_ctor_set(x_47, 6, x_17);
lean_ctor_set(x_47, 7, x_18);
lean_ctor_set(x_47, 8, x_19);
lean_ctor_set(x_47, 9, x_21);
lean_ctor_set(x_47, 10, x_22);
lean_ctor_set(x_47, 11, x_23);
lean_ctor_set(x_47, 12, x_24);
lean_ctor_set(x_47, 13, x_46);
lean_ctor_set(x_47, 14, x_25);
lean_ctor_set(x_47, 15, x_26);
lean_ctor_set(x_47, 16, x_27);
lean_ctor_set(x_47, 17, x_28);
lean_ctor_set_uint8(x_47, sizeof(void*)*18, x_20);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0;
x_51 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_4);
lean_ctor_set(x_51, 5, x_5);
lean_ctor_set(x_51, 6, x_6);
lean_ctor_set(x_51, 7, x_7);
lean_ctor_set(x_51, 8, x_8);
lean_ctor_set(x_51, 9, x_9);
lean_ctor_set(x_51, 10, x_10);
x_52 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_52, 0, x_11);
lean_ctor_set(x_52, 1, x_12);
lean_ctor_set(x_52, 2, x_13);
lean_ctor_set(x_52, 3, x_14);
lean_ctor_set(x_52, 4, x_15);
lean_ctor_set(x_52, 5, x_16);
lean_ctor_set(x_52, 6, x_17);
lean_ctor_set(x_52, 7, x_18);
lean_ctor_set(x_52, 8, x_19);
lean_ctor_set(x_52, 9, x_21);
lean_ctor_set(x_52, 10, x_22);
lean_ctor_set(x_52, 11, x_23);
lean_ctor_set(x_52, 12, x_24);
lean_ctor_set(x_52, 13, x_51);
lean_ctor_set(x_52, 14, x_25);
lean_ctor_set(x_52, 15, x_26);
lean_ctor_set(x_52, 16, x_27);
lean_ctor_set(x_52, 17, x_28);
lean_ctor_set_uint8(x_52, sizeof(void*)*18, x_20);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_29);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
lean_object* x_34 = _args[33];
lean_object* x_35 = _args[34];
lean_object* x_36 = _args[35];
lean_object* x_37 = _args[36];
lean_object* x_38 = _args[37];
lean_object* x_39 = _args[38];
_start:
{
uint8_t x_40; lean_object* x_41; 
x_40 = lean_unbox(x_20);
x_41 = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_40, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
return x_41;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 3);
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0;
lean_ctor_set(x_5, 3, x_10);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_5);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0;
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_20, x_2, x_22);
x_2 = x_24;
x_3 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_274; 
if (x_3 == 0)
{
uint8_t x_297; 
x_297 = l_Array_isEmpty___redArg(x_2);
if (x_297 == 0)
{
x_274 = x_297;
goto block_296;
}
else
{
lean_object* x_298; 
lean_dec_ref(x_1);
x_298 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_298;
}
}
else
{
uint8_t x_299; 
x_299 = 0;
x_274 = x_299;
goto block_296;
}
block_30:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(x_24, 0, x_14);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_25 = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(x_24, x_15, x_16, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = lean_apply_9(x_4, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, lean_box(0));
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
block_273:
{
lean_object* x_43; 
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
x_43 = l_Lean_Elab_Tactic_elabGrindParams(x_33, x_2, x_3, x_32, x_31, x_36, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_45);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_44, 8);
x_48 = lean_ctor_get(x_34, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_45, 3);
lean_dec(x_51);
lean_inc(x_47);
lean_ctor_set(x_45, 3, x_47);
lean_inc(x_44);
lean_ctor_set(x_34, 4, x_44);
if (x_3 == 0)
{
x_14 = x_44;
x_15 = x_34;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_52; 
x_52 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_54, 13);
lean_inc_ref(x_55);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_57 = lean_ctor_get(x_53, 1);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_54, 4);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_54, 5);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_54, 6);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_54, 7);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_54, 8);
lean_inc_ref(x_67);
x_68 = lean_ctor_get_uint8(x_54, sizeof(void*)*18);
x_69 = lean_ctor_get(x_54, 9);
lean_inc(x_69);
x_70 = lean_ctor_get(x_54, 10);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_54, 11);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_54, 12);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_54, 14);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_54, 15);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_54, 16);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_54, 17);
lean_inc_ref(x_76);
lean_dec_ref(x_54);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_55, 3);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_55, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_55, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_55, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_55, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_55, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_55, 9);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_55, 10);
lean_inc_ref(x_86);
lean_dec_ref(x_55);
x_87 = lean_box(x_68);
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(x_88, 0, x_78);
lean_closure_set(x_88, 1, x_79);
lean_closure_set(x_88, 2, x_77);
lean_closure_set(x_88, 3, x_80);
lean_closure_set(x_88, 4, x_81);
lean_closure_set(x_88, 5, x_82);
lean_closure_set(x_88, 6, x_83);
lean_closure_set(x_88, 7, x_84);
lean_closure_set(x_88, 8, x_85);
lean_closure_set(x_88, 9, x_86);
lean_closure_set(x_88, 10, x_59);
lean_closure_set(x_88, 11, x_60);
lean_closure_set(x_88, 12, x_61);
lean_closure_set(x_88, 13, x_62);
lean_closure_set(x_88, 14, x_63);
lean_closure_set(x_88, 15, x_64);
lean_closure_set(x_88, 16, x_65);
lean_closure_set(x_88, 17, x_66);
lean_closure_set(x_88, 18, x_67);
lean_closure_set(x_88, 19, x_87);
lean_closure_set(x_88, 20, x_69);
lean_closure_set(x_88, 21, x_70);
lean_closure_set(x_88, 22, x_71);
lean_closure_set(x_88, 23, x_72);
lean_closure_set(x_88, 24, x_73);
lean_closure_set(x_88, 25, x_74);
lean_closure_set(x_88, 26, x_75);
lean_closure_set(x_88, 27, x_76);
lean_closure_set(x_88, 28, x_57);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_34);
x_89 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_88, x_34, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_box(0);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 1, x_91);
lean_ctor_set(x_53, 0, x_90);
x_92 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_53, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_14 = x_44;
x_15 = x_34;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
uint8_t x_93; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
return x_92;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_free_object(x_53);
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_96 = !lean_is_exclusive(x_89);
if (x_96 == 0)
{
return x_89;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_99 = lean_ctor_get(x_53, 1);
lean_inc(x_99);
lean_dec(x_53);
x_100 = lean_ctor_get(x_54, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_54, 4);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_54, 5);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_54, 6);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_54, 7);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_54, 8);
lean_inc_ref(x_108);
x_109 = lean_ctor_get_uint8(x_54, sizeof(void*)*18);
x_110 = lean_ctor_get(x_54, 9);
lean_inc(x_110);
x_111 = lean_ctor_get(x_54, 10);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_54, 11);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_54, 12);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_54, 14);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_54, 15);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_54, 16);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_54, 17);
lean_inc_ref(x_117);
lean_dec_ref(x_54);
x_118 = lean_ctor_get(x_55, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_55, 3);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_55, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_55, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_55, 6);
lean_inc(x_123);
x_124 = lean_ctor_get(x_55, 7);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_55, 8);
lean_inc(x_125);
x_126 = lean_ctor_get(x_55, 9);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_55, 10);
lean_inc_ref(x_127);
lean_dec_ref(x_55);
x_128 = lean_box(x_109);
x_129 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(x_129, 0, x_119);
lean_closure_set(x_129, 1, x_120);
lean_closure_set(x_129, 2, x_118);
lean_closure_set(x_129, 3, x_121);
lean_closure_set(x_129, 4, x_122);
lean_closure_set(x_129, 5, x_123);
lean_closure_set(x_129, 6, x_124);
lean_closure_set(x_129, 7, x_125);
lean_closure_set(x_129, 8, x_126);
lean_closure_set(x_129, 9, x_127);
lean_closure_set(x_129, 10, x_100);
lean_closure_set(x_129, 11, x_101);
lean_closure_set(x_129, 12, x_102);
lean_closure_set(x_129, 13, x_103);
lean_closure_set(x_129, 14, x_104);
lean_closure_set(x_129, 15, x_105);
lean_closure_set(x_129, 16, x_106);
lean_closure_set(x_129, 17, x_107);
lean_closure_set(x_129, 18, x_108);
lean_closure_set(x_129, 19, x_128);
lean_closure_set(x_129, 20, x_110);
lean_closure_set(x_129, 21, x_111);
lean_closure_set(x_129, 22, x_112);
lean_closure_set(x_129, 23, x_113);
lean_closure_set(x_129, 24, x_114);
lean_closure_set(x_129, 25, x_115);
lean_closure_set(x_129, 26, x_116);
lean_closure_set(x_129, 27, x_117);
lean_closure_set(x_129, 28, x_99);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_34);
x_130 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_129, x_34, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_133, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_134) == 0)
{
lean_dec_ref(x_134);
x_14 = x_44;
x_15 = x_34;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_138 = lean_ctor_get(x_130, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_139 = x_130;
} else {
 lean_dec_ref(x_130);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_141 = !lean_is_exclusive(x_52);
if (x_141 == 0)
{
return x_52;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_52, 0);
lean_inc(x_142);
lean_dec(x_52);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_45, 0);
x_145 = lean_ctor_get(x_45, 1);
x_146 = lean_ctor_get(x_45, 2);
x_147 = lean_ctor_get_uint8(x_45, sizeof(void*)*7);
x_148 = lean_ctor_get_uint8(x_45, sizeof(void*)*7 + 1);
x_149 = lean_ctor_get(x_45, 4);
x_150 = lean_ctor_get(x_45, 5);
x_151 = lean_ctor_get(x_45, 6);
x_152 = lean_ctor_get_uint8(x_45, sizeof(void*)*7 + 2);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_45);
lean_inc(x_47);
x_153 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_47);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set(x_153, 6, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*7, x_147);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 1, x_148);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 2, x_152);
lean_inc(x_44);
lean_ctor_set(x_34, 4, x_44);
lean_ctor_set(x_34, 1, x_153);
if (x_3 == 0)
{
x_14 = x_44;
x_15 = x_34;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_154; 
x_154 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_156, 13);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 1);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_156, 2);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_156, 3);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_156, 4);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_156, 5);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_156, 6);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_156, 7);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_156, 8);
lean_inc_ref(x_168);
x_169 = lean_ctor_get_uint8(x_156, sizeof(void*)*18);
x_170 = lean_ctor_get(x_156, 9);
lean_inc(x_170);
x_171 = lean_ctor_get(x_156, 10);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_156, 11);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_156, 12);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_156, 14);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_156, 15);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_156, 16);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_156, 17);
lean_inc_ref(x_177);
lean_dec_ref(x_156);
x_178 = lean_ctor_get(x_157, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_157, 3);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_157, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_157, 5);
lean_inc(x_182);
x_183 = lean_ctor_get(x_157, 6);
lean_inc(x_183);
x_184 = lean_ctor_get(x_157, 7);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_157, 8);
lean_inc(x_185);
x_186 = lean_ctor_get(x_157, 9);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_157, 10);
lean_inc_ref(x_187);
lean_dec_ref(x_157);
x_188 = lean_box(x_169);
x_189 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(x_189, 0, x_179);
lean_closure_set(x_189, 1, x_180);
lean_closure_set(x_189, 2, x_178);
lean_closure_set(x_189, 3, x_181);
lean_closure_set(x_189, 4, x_182);
lean_closure_set(x_189, 5, x_183);
lean_closure_set(x_189, 6, x_184);
lean_closure_set(x_189, 7, x_185);
lean_closure_set(x_189, 8, x_186);
lean_closure_set(x_189, 9, x_187);
lean_closure_set(x_189, 10, x_160);
lean_closure_set(x_189, 11, x_161);
lean_closure_set(x_189, 12, x_162);
lean_closure_set(x_189, 13, x_163);
lean_closure_set(x_189, 14, x_164);
lean_closure_set(x_189, 15, x_165);
lean_closure_set(x_189, 16, x_166);
lean_closure_set(x_189, 17, x_167);
lean_closure_set(x_189, 18, x_168);
lean_closure_set(x_189, 19, x_188);
lean_closure_set(x_189, 20, x_170);
lean_closure_set(x_189, 21, x_171);
lean_closure_set(x_189, 22, x_172);
lean_closure_set(x_189, 23, x_173);
lean_closure_set(x_189, 24, x_174);
lean_closure_set(x_189, 25, x_175);
lean_closure_set(x_189, 26, x_176);
lean_closure_set(x_189, 27, x_177);
lean_closure_set(x_189, 28, x_158);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_34);
x_190 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_189, x_34, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_159;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_193, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_194) == 0)
{
lean_dec_ref(x_194);
x_14 = x_44;
x_15 = x_34;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_159);
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_198 = lean_ctor_get(x_190, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_199 = x_190;
} else {
 lean_dec_ref(x_190);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec_ref(x_34);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_201 = lean_ctor_get(x_154, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_202 = x_154;
} else {
 lean_dec_ref(x_154);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_204 = lean_ctor_get(x_44, 8);
x_205 = lean_ctor_get(x_34, 0);
x_206 = lean_ctor_get(x_34, 2);
x_207 = lean_ctor_get(x_34, 3);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_34);
x_208 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_45, 2);
lean_inc_ref(x_210);
x_211 = lean_ctor_get_uint8(x_45, sizeof(void*)*7);
x_212 = lean_ctor_get_uint8(x_45, sizeof(void*)*7 + 1);
x_213 = lean_ctor_get(x_45, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_45, 5);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_45, 6);
lean_inc_ref(x_215);
x_216 = lean_ctor_get_uint8(x_45, sizeof(void*)*7 + 2);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 lean_ctor_release(x_45, 5);
 lean_ctor_release(x_45, 6);
 x_217 = x_45;
} else {
 lean_dec_ref(x_45);
 x_217 = lean_box(0);
}
lean_inc(x_204);
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 7, 3);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_209);
lean_ctor_set(x_218, 2, x_210);
lean_ctor_set(x_218, 3, x_204);
lean_ctor_set(x_218, 4, x_213);
lean_ctor_set(x_218, 5, x_214);
lean_ctor_set(x_218, 6, x_215);
lean_ctor_set_uint8(x_218, sizeof(void*)*7, x_211);
lean_ctor_set_uint8(x_218, sizeof(void*)*7 + 1, x_212);
lean_ctor_set_uint8(x_218, sizeof(void*)*7 + 2, x_216);
lean_inc(x_44);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_205);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_206);
lean_ctor_set(x_219, 3, x_207);
lean_ctor_set(x_219, 4, x_44);
if (x_3 == 0)
{
x_14 = x_44;
x_15 = x_219;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_220; 
x_220 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_222, 13);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_222, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 1);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_222, 2);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_222, 3);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_222, 4);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_222, 5);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_222, 6);
lean_inc_ref(x_232);
x_233 = lean_ctor_get(x_222, 7);
lean_inc_ref(x_233);
x_234 = lean_ctor_get(x_222, 8);
lean_inc_ref(x_234);
x_235 = lean_ctor_get_uint8(x_222, sizeof(void*)*18);
x_236 = lean_ctor_get(x_222, 9);
lean_inc(x_236);
x_237 = lean_ctor_get(x_222, 10);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_222, 11);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_222, 12);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_222, 14);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_222, 15);
lean_inc_ref(x_241);
x_242 = lean_ctor_get(x_222, 16);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_222, 17);
lean_inc_ref(x_243);
lean_dec_ref(x_222);
x_244 = lean_ctor_get(x_223, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_223, 2);
lean_inc_ref(x_245);
x_246 = lean_ctor_get(x_223, 3);
lean_inc_ref(x_246);
x_247 = lean_ctor_get(x_223, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_223, 5);
lean_inc(x_248);
x_249 = lean_ctor_get(x_223, 6);
lean_inc(x_249);
x_250 = lean_ctor_get(x_223, 7);
lean_inc_ref(x_250);
x_251 = lean_ctor_get(x_223, 8);
lean_inc(x_251);
x_252 = lean_ctor_get(x_223, 9);
lean_inc_ref(x_252);
x_253 = lean_ctor_get(x_223, 10);
lean_inc_ref(x_253);
lean_dec_ref(x_223);
x_254 = lean_box(x_235);
x_255 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(x_255, 0, x_245);
lean_closure_set(x_255, 1, x_246);
lean_closure_set(x_255, 2, x_244);
lean_closure_set(x_255, 3, x_247);
lean_closure_set(x_255, 4, x_248);
lean_closure_set(x_255, 5, x_249);
lean_closure_set(x_255, 6, x_250);
lean_closure_set(x_255, 7, x_251);
lean_closure_set(x_255, 8, x_252);
lean_closure_set(x_255, 9, x_253);
lean_closure_set(x_255, 10, x_226);
lean_closure_set(x_255, 11, x_227);
lean_closure_set(x_255, 12, x_228);
lean_closure_set(x_255, 13, x_229);
lean_closure_set(x_255, 14, x_230);
lean_closure_set(x_255, 15, x_231);
lean_closure_set(x_255, 16, x_232);
lean_closure_set(x_255, 17, x_233);
lean_closure_set(x_255, 18, x_234);
lean_closure_set(x_255, 19, x_254);
lean_closure_set(x_255, 20, x_236);
lean_closure_set(x_255, 21, x_237);
lean_closure_set(x_255, 22, x_238);
lean_closure_set(x_255, 23, x_239);
lean_closure_set(x_255, 24, x_240);
lean_closure_set(x_255, 25, x_241);
lean_closure_set(x_255, 26, x_242);
lean_closure_set(x_255, 27, x_243);
lean_closure_set(x_255, 28, x_224);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_219);
x_256 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_255, x_219, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_box(0);
if (lean_is_scalar(x_225)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_225;
 lean_ctor_set_tag(x_259, 1);
}
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_259, x_35, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_260) == 0)
{
lean_dec_ref(x_260);
x_14 = x_44;
x_15 = x_219;
x_16 = x_35;
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec_ref(x_219);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_262 = x_260;
} else {
 lean_dec_ref(x_260);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_225);
lean_dec_ref(x_219);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_264 = lean_ctor_get(x_256, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_265 = x_256;
} else {
 lean_dec_ref(x_256);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_219);
lean_dec(x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_4);
x_267 = lean_ctor_get(x_220, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_268 = x_220;
} else {
 lean_dec_ref(x_220);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
return x_269;
}
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_4);
x_270 = !lean_is_exclusive(x_43);
if (x_270 == 0)
{
return x_43;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_43, 0);
lean_inc(x_271);
lean_dec(x_43);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
}
block_296:
{
uint8_t x_275; 
x_275 = 1;
if (x_3 == 0)
{
x_31 = x_275;
x_32 = x_274;
x_33 = x_1;
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = x_11;
x_41 = x_12;
x_42 = lean_box(0);
goto block_273;
}
else
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_1);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; size_t x_279; size_t x_280; lean_object* x_281; lean_object* x_282; 
x_277 = lean_ctor_get(x_1, 1);
x_278 = lean_ctor_get(x_1, 8);
lean_dec(x_278);
x_279 = lean_array_size(x_277);
x_280 = 0;
x_281 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(x_279, x_280, x_277);
x_282 = lean_box(0);
lean_ctor_set(x_1, 8, x_282);
lean_ctor_set(x_1, 1, x_281);
x_31 = x_275;
x_32 = x_274;
x_33 = x_1;
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = x_11;
x_41 = x_12;
x_42 = lean_box(0);
goto block_273;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; size_t x_291; size_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_283 = lean_ctor_get(x_1, 0);
x_284 = lean_ctor_get(x_1, 1);
x_285 = lean_ctor_get(x_1, 2);
x_286 = lean_ctor_get(x_1, 3);
x_287 = lean_ctor_get(x_1, 4);
x_288 = lean_ctor_get(x_1, 5);
x_289 = lean_ctor_get(x_1, 6);
x_290 = lean_ctor_get(x_1, 7);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_1);
x_291 = lean_array_size(x_284);
x_292 = 0;
x_293 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(x_291, x_292, x_284);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_295, 0, x_283);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_285);
lean_ctor_set(x_295, 3, x_286);
lean_ctor_set(x_295, 4, x_287);
lean_ctor_set(x_295, 5, x_288);
lean_ctor_set(x_295, 6, x_289);
lean_ctor_set(x_295, 7, x_290);
lean_ctor_set(x_295, 8, x_294);
x_31 = x_275;
x_32 = x_274;
x_33 = x_295;
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = x_11;
x_41 = x_12;
x_42 = lean_box(0);
goto block_273;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Elab_Tactic_Grind_withParams___redArg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Grind_withParams___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
x_16 = l_Lean_Elab_Tactic_Grind_withParams(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
return x_16;
}
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1 = _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__6);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
l_Lean_Elab_Tactic_addEMatchTheorem___closed__1 = _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
l_Lean_Elab_Tactic_addEMatchTheorem___closed__3 = _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
l_Lean_Elab_Tactic_addEMatchTheorem___closed__5 = _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
l_Lean_Elab_Tactic_addEMatchTheorem___closed__7 = _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
l_Lean_Elab_Tactic_addEMatchTheorem___closed__9 = _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1 = _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1();
lean_mark_persistent(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1);
l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3 = _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3();
lean_mark_persistent(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__2);
l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
