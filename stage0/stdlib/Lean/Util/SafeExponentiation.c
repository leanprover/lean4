// Lean compiler output
// Module: Lean.Util.SafeExponentiation
// Imports: public import Lean.CoreM
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_recordOptionAccess(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "exponentiation"};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(83, 126, 177, 93, 34, 88, 85, 55)}};
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 127, 45, 106, 162, 118, 90, 191)}};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 300, .m_capacity = 300, .m_length = 299, .m_data = "maximum value for which exponentiation operations are safe to evaluate. When an exponent is a value greater than this threshold, the exponentiation will not be evaluated, and a warning will be logged. This helps to prevent the system from becoming unresponsive due to excessively large computations."};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(66, 195, 247, 99, 191, 194, 19, 186)}};
static const lean_ctor_object l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 37, 3, 64, 108, 254, 216, 252)}};
static const lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exponentiation_threshold;
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkExponent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l_Lean_checkExponent___closed__0 = (const lean_object*)&l_Lean_checkExponent___closed__0_value;
static const lean_ctor_object l_Lean_checkExponent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkExponent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 119, 170, 15, 163, 222, 21)}};
static const lean_ctor_object l_Lean_checkExponent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_checkExponent___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(50, 3, 22, 131, 26, 69, 126, 0)}};
static const lean_object* l_Lean_checkExponent___closed__1 = (const lean_object*)&l_Lean_checkExponent___closed__1_value;
static const lean_string_object l_Lean_checkExponent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_checkExponent___closed__2 = (const lean_object*)&l_Lean_checkExponent___closed__2_value;
static const lean_string_object l_Lean_checkExponent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " exceeds the threshold "};
static const lean_object* l_Lean_checkExponent___closed__3 = (const lean_object*)&l_Lean_checkExponent___closed__3_value;
static const lean_string_object l_Lean_checkExponent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = ", exponentiation operation was not evaluated, use `set_option "};
static const lean_object* l_Lean_checkExponent___closed__4 = (const lean_object*)&l_Lean_checkExponent___closed__4_value;
static const lean_string_object l_Lean_checkExponent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " <num>` to set a new threshold"};
static const lean_object* l_Lean_checkExponent___closed__5 = (const lean_object*)&l_Lean_checkExponent___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
lean_inc(v_defValue_5_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v_defValue_5_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_9_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_9_, 0, v_name_1_);
lean_ctor_set(v___x_9_, 1, v_ref_3_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v_descr_6_);
lean_ctor_set(v___x_9_, 4, v_deprecation_x3f_7_);
v___x_10_ = lean_register_option(v_name_1_, v___x_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 0);
lean_dec(v_unused_19_);
v___x_12_ = v___x_10_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_dec(v___x_10_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_defValue_5_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_name_1_);
lean_ctor_set(v___x_14_, 1, v_defValue_5_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_name_1_);
v_a_20_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_10_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_10_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_50_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_52_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v___x_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(lean_object* v_opt_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_toCold_59_; lean_object* v_options_60_; lean_object* v_name_61_; lean_object* v_defValue_62_; lean_object* v_map_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_toCold_59_ = lean_ctor_get(v_a_56_, 0);
v_options_60_ = lean_ctor_get(v_toCold_59_, 2);
v_name_61_ = lean_ctor_get(v_opt_55_, 0);
lean_inc(v_name_61_);
v_defValue_62_ = lean_ctor_get(v_opt_55_, 1);
lean_inc(v_defValue_62_);
lean_dec_ref(v_opt_55_);
v_map_63_ = lean_ctor_get(v_options_60_, 0);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_63_, v_name_61_);
v___x_65_ = l___private_Lean_CoreM_0__Lean_recordOptionAccess(v_name_61_, v___x_64_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_80_; 
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_81_);
v___x_67_ = v___x_65_;
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_65_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v_defValue_62_);
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_defValue_62_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
lean_object* v_val_72_; 
v_val_72_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_val_72_);
lean_dec_ref_known(v___x_64_, 1);
if (lean_obj_tag(v_val_72_) == 3)
{
lean_object* v_v_73_; lean_object* v___x_75_; 
lean_dec(v_defValue_62_);
v_v_73_ = lean_ctor_get(v_val_72_, 0);
lean_inc(v_v_73_);
lean_dec_ref_known(v_val_72_, 1);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v_v_73_);
v___x_75_ = v___x_67_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_v_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v_val_72_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v_defValue_62_);
v___x_78_ = v___x_67_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_defValue_62_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec(v___x_64_);
lean_dec(v_defValue_62_);
v_a_82_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_65_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_65_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0___boxed(lean_object* v_opt_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v_opt_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
lean_object* v_name_97_; lean_object* v_defValue_98_; lean_object* v_map_99_; lean_object* v___x_100_; 
v_name_97_ = lean_ctor_get(v_opt_96_, 0);
v_defValue_98_ = lean_ctor_get(v_opt_96_, 1);
v_map_99_ = lean_ctor_get(v_opts_95_, 0);
v___x_100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_99_, v_name_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
uint8_t v___x_101_; 
v___x_101_ = lean_unbox(v_defValue_98_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; 
v_val_102_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v___x_100_, 1);
if (lean_obj_tag(v_val_102_) == 1)
{
uint8_t v_v_103_; 
v_v_103_ = lean_ctor_get_uint8(v_val_102_, 0);
lean_dec_ref_known(v_val_102_, 0);
return v_v_103_;
}
else
{
uint8_t v___x_104_; 
lean_dec(v_val_102_);
v___x_104_ = lean_unbox(v_defValue_98_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_105_, lean_object* v_opt_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_105_, v_opt_106_);
lean_dec_ref(v_opt_106_);
lean_dec_ref(v_opts_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_109_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
lean_ctor_set(v___x_115_, 3, v___x_114_);
lean_ctor_set(v___x_115_, 4, v___x_113_);
lean_ctor_set(v___x_115_, 5, v___x_113_);
lean_ctor_set(v___x_115_, 6, v___x_113_);
lean_ctor_set(v___x_115_, 7, v___x_113_);
lean_ctor_set(v___x_115_, 8, v___x_113_);
lean_ctor_set(v___x_115_, 9, v___x_113_);
lean_ctor_set(v___x_115_, 10, v___x_113_);
lean_ctor_set(v___x_115_, 11, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(32u);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_119_ = ((size_t)5ULL);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_unsigned_to_nat(32u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3);
v___x_124_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_120_);
lean_ctor_set(v___x_124_, 3, v___x_120_);
lean_ctor_set_usize(v___x_124_, 4, v___x_119_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_box(1);
v___x_126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4);
v___x_127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(lean_object* v_msgData_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_toCold_134_; lean_object* v_env_135_; lean_object* v_options_136_; uint8_t v___x_137_; lean_object* v_env_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_toCold_134_ = lean_ctor_get(v___y_130_, 0);
v_env_135_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_133_);
v_options_136_ = lean_ctor_get(v_toCold_134_, 2);
v___x_137_ = 0;
v_env_138_ = l_Lean_Environment_setRecordingDeps(v_env_135_, v___x_137_);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2);
v___x_140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_136_);
v___x_141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_141_, 0, v_env_138_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_140_);
lean_ctor_set(v___x_141_, 3, v_options_136_);
v___x_142_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v_msgData_129_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_msgData_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 1)
{
lean_object* v_pre_159_; 
v_pre_159_ = lean_ctor_get(v_x_158_, 0);
switch(lean_obj_tag(v_pre_159_))
{
case 1:
{
lean_object* v_pre_160_; 
v_pre_160_ = lean_ctor_get(v_pre_159_, 0);
switch(lean_obj_tag(v_pre_160_))
{
case 0:
{
lean_object* v_str_161_; lean_object* v_str_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_str_161_ = lean_ctor_get(v_x_158_, 1);
v_str_162_ = lean_ctor_get(v_pre_159_, 1);
v___x_163_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_164_ = lean_string_dec_eq(v_str_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_166_ = lean_string_dec_eq(v_str_162_, v___x_165_);
if (v___x_166_ == 0)
{
return v___x_166_;
}
else
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_168_ = lean_string_dec_eq(v_str_161_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
return v_suppressElabErrors_157_;
}
}
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_170_ = lean_string_dec_eq(v_str_161_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
return v_suppressElabErrors_157_;
}
}
}
case 1:
{
lean_object* v_pre_171_; 
v_pre_171_ = lean_ctor_get(v_pre_160_, 0);
if (lean_obj_tag(v_pre_171_) == 0)
{
lean_object* v_str_172_; lean_object* v_str_173_; lean_object* v_str_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_str_172_ = lean_ctor_get(v_x_158_, 1);
v_str_173_ = lean_ctor_get(v_pre_159_, 1);
v_str_174_ = lean_ctor_get(v_pre_160_, 1);
v___x_175_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_176_ = lean_string_dec_eq(v_str_174_, v___x_175_);
if (v___x_176_ == 0)
{
return v___x_176_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_178_ = lean_string_dec_eq(v_str_173_, v___x_177_);
if (v___x_178_ == 0)
{
return v___x_178_;
}
else
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6));
v___x_180_ = lean_string_dec_eq(v_str_172_, v___x_179_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
return v_suppressElabErrors_157_;
}
}
}
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
default: 
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
case 0:
{
lean_object* v_str_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_str_183_ = lean_ctor_get(v_x_158_, 1);
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7));
v___x_185_ = lean_string_dec_eq(v_str_183_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
return v_suppressElabErrors_157_;
}
}
default: 
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
}
else
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_suppressElabErrors_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_suppressElabErrors_boxed_190_ = lean_unbox(v_suppressElabErrors_188_);
v_res_191_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_190_, v_x_189_);
lean_dec(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(lean_object* v_ref_194_, lean_object* v_msgData_195_, uint8_t v_severity_196_, uint8_t v_isSilent_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v___y_202_; lean_object* v___y_203_; uint8_t v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v_toCold_209_; lean_object* v___y_210_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; uint8_t v___y_242_; lean_object* v___y_243_; uint8_t v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_266_; lean_object* v___y_267_; uint8_t v___y_268_; uint8_t v___y_269_; uint8_t v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; uint8_t v___y_276_; uint8_t v___y_277_; uint8_t v___x_287_; uint8_t v___y_289_; uint8_t v___x_295_; 
v___x_287_ = 2;
v___x_295_ = l_Lean_instBEqMessageSeverity_beq(v_severity_196_, v___x_287_);
if (v___x_295_ == 0)
{
v___y_289_ = v___x_295_;
goto v___jp_288_;
}
else
{
uint8_t v___x_296_; 
lean_inc_ref(v_msgData_195_);
v___x_296_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_195_);
if (v___x_296_ == 0)
{
v___y_289_ = v___x_296_;
goto v___jp_288_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_msgData_195_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
v___jp_201_:
{
lean_object* v_currNamespace_211_; lean_object* v_openDecls_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_env_217_; lean_object* v_nextMacroScope_218_; lean_object* v_ngen_219_; lean_object* v_auxDeclNGen_220_; lean_object* v_traceState_221_; lean_object* v_cache_222_; lean_object* v_recordedDeps_223_; lean_object* v_messages_224_; lean_object* v_infoState_225_; lean_object* v_snapshotTasks_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_237_; 
v_currNamespace_211_ = lean_ctor_get(v_toCold_209_, 4);
v_openDecls_212_ = lean_ctor_get(v_toCold_209_, 5);
lean_inc(v_openDecls_212_);
lean_inc(v_currNamespace_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_currNamespace_211_);
lean_ctor_set(v___x_213_, 1, v_openDecls_212_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___y_206_);
lean_inc_ref(v___y_208_);
lean_inc_ref(v___y_205_);
v___x_215_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_215_, 0, v___y_205_);
lean_ctor_set(v___x_215_, 1, v___y_203_);
lean_ctor_set(v___x_215_, 2, v___y_207_);
lean_ctor_set(v___x_215_, 3, v___y_208_);
lean_ctor_set(v___x_215_, 4, v___x_214_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5, v___y_202_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5 + 1, v___y_204_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5 + 2, v_isSilent_197_);
v___x_216_ = lean_st_ref_take(v___y_210_);
v_env_217_ = lean_ctor_get(v___x_216_, 0);
v_nextMacroScope_218_ = lean_ctor_get(v___x_216_, 1);
v_ngen_219_ = lean_ctor_get(v___x_216_, 2);
v_auxDeclNGen_220_ = lean_ctor_get(v___x_216_, 3);
v_traceState_221_ = lean_ctor_get(v___x_216_, 4);
v_cache_222_ = lean_ctor_get(v___x_216_, 5);
v_recordedDeps_223_ = lean_ctor_get(v___x_216_, 6);
v_messages_224_ = lean_ctor_get(v___x_216_, 7);
v_infoState_225_ = lean_ctor_get(v___x_216_, 8);
v_snapshotTasks_226_ = lean_ctor_get(v___x_216_, 9);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_237_ == 0)
{
v___x_228_ = v___x_216_;
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_snapshotTasks_226_);
lean_inc(v_infoState_225_);
lean_inc(v_messages_224_);
lean_inc(v_recordedDeps_223_);
lean_inc(v_cache_222_);
lean_inc(v_traceState_221_);
lean_inc(v_auxDeclNGen_220_);
lean_inc(v_ngen_219_);
lean_inc(v_nextMacroScope_218_);
lean_inc(v_env_217_);
lean_dec(v___x_216_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v___x_231_ = l_Lean_MessageLog_add(v___x_215_, v_messages_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 7, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_env_217_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_nextMacroScope_218_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_ngen_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_auxDeclNGen_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_traceState_221_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_cache_222_);
lean_ctor_set(v_reuseFailAlloc_236_, 6, v_recordedDeps_223_);
lean_ctor_set(v_reuseFailAlloc_236_, 7, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 8, v_infoState_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 9, v_snapshotTasks_226_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v___y_210_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_230_);
return v___x_235_;
}
}
}
v___jp_238_:
{
lean_object* v_fileName_247_; lean_object* v_fileMap_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_264_; 
v_fileName_247_ = lean_ctor_get(v___y_243_, 0);
v_fileMap_248_ = lean_ctor_get(v___y_243_, 1);
v___x_249_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_195_);
v___x_250_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v___x_249_, v___y_198_, v___y_199_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_264_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_inc_ref_n(v_fileMap_248_, 2);
v___x_255_ = l_Lean_FileMap_toPosition(v_fileMap_248_, v___y_245_);
lean_dec(v___y_245_);
v___x_256_ = l_Lean_FileMap_toPosition(v_fileMap_248_, v___y_246_);
lean_dec(v___y_246_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0));
if (v___y_244_ == 0)
{
lean_del_object(v___x_253_);
lean_dec_ref(v___y_239_);
v___y_202_ = v___y_241_;
v___y_203_ = v___x_255_;
v___y_204_ = v___y_242_;
v___y_205_ = v_fileName_247_;
v___y_206_ = v_a_251_;
v___y_207_ = v___x_257_;
v___y_208_ = v___x_258_;
v_toCold_209_ = v___y_240_;
v___y_210_ = v___y_199_;
goto v___jp_201_;
}
else
{
uint8_t v___x_259_; 
lean_inc(v_a_251_);
v___x_259_ = l_Lean_MessageData_hasTag(v___y_239_, v_a_251_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_257_, 1);
lean_dec_ref(v___x_255_);
lean_dec(v_a_251_);
v___x_260_ = lean_box(0);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_260_);
v___x_262_ = v___x_253_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_del_object(v___x_253_);
v___y_202_ = v___y_241_;
v___y_203_ = v___x_255_;
v___y_204_ = v___y_242_;
v___y_205_ = v_fileName_247_;
v___y_206_ = v_a_251_;
v___y_207_ = v___x_257_;
v___y_208_ = v___x_258_;
v_toCold_209_ = v___y_240_;
v___y_210_ = v___y_199_;
goto v___jp_201_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Syntax_getTailPos_x3f(v___y_271_, v___y_269_);
lean_dec(v___y_271_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_inc(v___y_272_);
v___y_239_ = v___y_266_;
v___y_240_ = v___y_267_;
v___y_241_ = v___y_269_;
v___y_242_ = v___y_270_;
v___y_243_ = v___y_267_;
v___y_244_ = v___y_268_;
v___y_245_ = v___y_272_;
v___y_246_ = v___y_272_;
goto v___jp_238_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_273_, 1);
v___y_239_ = v___y_266_;
v___y_240_ = v___y_267_;
v___y_241_ = v___y_269_;
v___y_242_ = v___y_270_;
v___y_243_ = v___y_267_;
v___y_244_ = v___y_268_;
v___y_245_ = v___y_272_;
v___y_246_ = v_val_274_;
goto v___jp_238_;
}
}
v___jp_275_:
{
lean_object* v_toCold_278_; lean_object* v_ref_279_; uint8_t v_suppressElabErrors_280_; lean_object* v___x_281_; lean_object* v___f_282_; lean_object* v_ref_283_; lean_object* v___x_284_; 
v_toCold_278_ = lean_ctor_get(v___y_198_, 0);
v_ref_279_ = lean_ctor_get(v___y_198_, 2);
v_suppressElabErrors_280_ = lean_ctor_get_uint8(v___y_198_, sizeof(void*)*3 + 2);
v___x_281_ = lean_box(v_suppressElabErrors_280_);
v___f_282_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_282_, 0, v___x_281_);
v_ref_283_ = l_Lean_replaceRef(v_ref_194_, v_ref_279_);
v___x_284_ = l_Lean_Syntax_getPos_x3f(v_ref_283_, v___y_276_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___y_266_ = v___f_282_;
v___y_267_ = v_toCold_278_;
v___y_268_ = v_suppressElabErrors_280_;
v___y_269_ = v___y_276_;
v___y_270_ = v___y_277_;
v___y_271_ = v_ref_283_;
v___y_272_ = v___x_285_;
goto v___jp_265_;
}
else
{
lean_object* v_val_286_; 
v_val_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_284_, 1);
v___y_266_ = v___f_282_;
v___y_267_ = v_toCold_278_;
v___y_268_ = v_suppressElabErrors_280_;
v___y_269_ = v___y_276_;
v___y_270_ = v___y_277_;
v___y_271_ = v_ref_283_;
v___y_272_ = v_val_286_;
goto v___jp_265_;
}
}
v___jp_288_:
{
uint8_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 1;
v___x_291_ = l_Lean_instBEqMessageSeverity_beq(v_severity_196_, v___x_290_);
if (v___x_291_ == 0)
{
v___y_276_ = v___y_289_;
v___y_277_ = v_severity_196_;
goto v___jp_275_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_198_);
v___x_293_ = l_Lean_warningAsError;
v___x_294_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v___x_292_, v___x_293_);
lean_dec_ref(v___x_292_);
if (v___x_294_ == 0)
{
v___y_276_ = v___y_289_;
v___y_277_ = v_severity_196_;
goto v___jp_275_;
}
else
{
v___y_276_ = v___y_289_;
v___y_277_ = v___x_287_;
goto v___jp_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_299_, lean_object* v_msgData_300_, lean_object* v_severity_301_, lean_object* v_isSilent_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_severity_boxed_306_; uint8_t v_isSilent_boxed_307_; lean_object* v_res_308_; 
v_severity_boxed_306_ = lean_unbox(v_severity_301_);
v_isSilent_boxed_307_ = lean_unbox(v_isSilent_302_);
v_res_308_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_299_, v_msgData_300_, v_severity_boxed_306_, v_isSilent_boxed_307_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v_ref_299_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(lean_object* v_msgData_309_, uint8_t v_severity_310_, uint8_t v_isSilent_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_ref_315_; lean_object* v___x_316_; 
v_ref_315_ = lean_ctor_get(v___y_312_, 2);
v___x_316_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_315_, v_msgData_309_, v_severity_310_, v_isSilent_311_, v___y_312_, v___y_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(lean_object* v_msgData_317_, lean_object* v_severity_318_, lean_object* v_isSilent_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v_severity_boxed_323_; uint8_t v_isSilent_boxed_324_; lean_object* v_res_325_; 
v_severity_boxed_323_ = lean_unbox(v_severity_318_);
v_isSilent_boxed_324_ = lean_unbox(v_isSilent_319_);
v_res_325_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_317_, v_severity_boxed_323_, v_isSilent_boxed_324_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v___x_330_ = 1;
v___x_331_ = 0;
v___x_332_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_326_, v___x_330_, v___x_331_, v___y_327_, v___y_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v_msgData_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object* v_n_346_, uint8_t v_warning_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Lean_exponentiation_threshold;
v___x_356_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v___x_355_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_403_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_403_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_403_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_403_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_lt(v_a_357_, v_n_346_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
lean_dec(v_a_357_);
lean_dec(v_n_346_);
v___x_362_ = 1;
v___x_363_ = lean_box(v___x_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_363_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_del_object(v___x_359_);
if (v_warning_347_ == 0)
{
lean_dec(v_a_357_);
lean_dec(v_n_346_);
goto v___jp_351_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_checkExponent___closed__1));
v___x_368_ = l_Lean_logMessageKind___redArg(v___x_367_, v_a_349_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_402_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_402_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_402_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_402_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_unbox(v_a_369_);
if (v___x_373_ == 0)
{
lean_del_object(v___x_371_);
lean_dec(v_a_369_);
lean_dec(v_a_357_);
lean_dec(v_n_346_);
goto v___jp_351_;
}
else
{
lean_object* v_name_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v_name_374_ = lean_ctor_get(v___x_355_, 0);
v___x_375_ = ((lean_object*)(l_Lean_checkExponent___closed__2));
v___x_376_ = l_Nat_reprFast(v_n_346_);
v___x_377_ = lean_string_append(v___x_375_, v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = ((lean_object*)(l_Lean_checkExponent___closed__3));
v___x_379_ = lean_string_append(v___x_377_, v___x_378_);
v___x_380_ = l_Nat_reprFast(v_a_357_);
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = ((lean_object*)(l_Lean_checkExponent___closed__4));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
v___x_384_ = lean_unbox(v_a_369_);
lean_dec(v_a_369_);
lean_inc(v_name_374_);
v___x_385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_374_, v___x_384_);
v___x_386_ = lean_string_append(v___x_383_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_checkExponent___closed__5));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 3);
lean_ctor_set(v___x_371_, 0, v___x_388_);
v___x_390_ = v___x_371_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_401_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_MessageData_ofFormat(v___x_390_);
v___x_392_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v___x_391_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
goto v___jp_351_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_357_);
lean_dec(v_n_346_);
return v___x_368_;
}
}
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_n_346_);
v_a_404_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_356_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_356_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
v___jp_351_:
{
uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = 0;
v___x_353_ = lean_box(v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object* v_n_412_, lean_object* v_warning_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_warning_boxed_417_; lean_object* v_res_418_; 
v_warning_boxed_417_ = lean_unbox(v_warning_413_);
v_res_418_ = l_Lean_checkExponent(v_n_412_, v_warning_boxed_417_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_418_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_exponentiation_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exponentiation_threshold);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_SafeExponentiation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_SafeExponentiation(builtin);
}
#ifdef __cplusplus
}
#endif
