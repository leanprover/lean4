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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_53_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT void l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
return v_res_56_;
}
}
lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(lean_object* v_opt_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_toCold_61_; lean_object* v_options_62_; lean_object* v_name_63_; lean_object* v_defValue_64_; lean_object* v_map_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_toCold_61_ = lean_ctor_get(v_a_58_, 0);
v_options_62_ = lean_ctor_get(v_toCold_61_, 2);
v_name_63_ = lean_ctor_get(v_opt_57_, 0);
lean_inc(v_name_63_);
v_defValue_64_ = lean_ctor_get(v_opt_57_, 1);
lean_inc(v_defValue_64_);
lean_dec_ref(v_opt_57_);
v_map_65_ = lean_ctor_get(v_options_62_, 0);
v___x_66_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_65_, v_name_63_);
v___x_67_ = l___private_Lean_CoreM_0__Lean_recordOptionAccess(v_name_63_, v___x_66_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_82_; 
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v___x_67_, 0);
lean_dec(v_unused_83_);
v___x_69_ = v___x_67_;
v_isShared_70_ = v_isSharedCheck_82_;
goto v_resetjp_68_;
}
else
{
lean_dec(v___x_67_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_82_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_defValue_64_);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_defValue_64_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
else
{
lean_object* v_val_74_; 
v_val_74_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v___x_66_, 1);
if (lean_obj_tag(v_val_74_) == 3)
{
lean_object* v_v_75_; lean_object* v___x_77_; 
lean_dec(v_defValue_64_);
v_v_75_ = lean_ctor_get(v_val_74_, 0);
lean_inc(v_v_75_);
lean_dec_ref_known(v_val_74_, 1);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_v_75_);
v___x_77_ = v___x_69_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_v_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_val_74_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_defValue_64_);
v___x_80_ = v___x_69_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_defValue_64_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec(v___x_66_);
lean_dec(v_defValue_64_);
v_a_84_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_67_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_67_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_a_59_ = stack[2].m_obj;
lean_object* v_res_92_;
v_res_92_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v_opt_57_, v_a_58_, v_a_59_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0___boxed(lean_object* v_opt_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v_opt_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_97_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_98_, lean_object* v_opt_99_){
_start:
{
lean_object* v_name_100_; lean_object* v_defValue_101_; lean_object* v_map_102_; lean_object* v___x_103_; 
v_name_100_ = lean_ctor_get(v_opt_99_, 0);
v_defValue_101_ = lean_ctor_get(v_opt_99_, 1);
v_map_102_ = lean_ctor_get(v_opts_98_, 0);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_102_, v_name_100_);
if (lean_obj_tag(v___x_103_) == 0)
{
uint8_t v___x_104_; 
v___x_104_ = lean_unbox(v_defValue_101_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v___x_103_, 1);
if (lean_obj_tag(v_val_105_) == 1)
{
uint8_t v_v_106_; 
v_v_106_ = lean_ctor_get_uint8(v_val_105_, 0);
lean_dec_ref_known(v_val_105_, 0);
return v_v_106_;
}
else
{
uint8_t v___x_107_; 
lean_dec(v_val_105_);
v___x_107_ = lean_unbox(v_defValue_101_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_98_ = stack[0].m_obj;
lean_object* v_opt_99_ = stack[1].m_obj;
uint8_t v_res_108_;
v_res_108_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_98_, v_opt_99_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_109_, lean_object* v_opt_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_109_, v_opt_110_);
lean_dec_ref(v_opt_110_);
lean_dec_ref(v_opts_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
lean_ctor_set(v___x_119_, 3, v___x_118_);
lean_ctor_set(v___x_119_, 4, v___x_117_);
lean_ctor_set(v___x_119_, 5, v___x_117_);
lean_ctor_set(v___x_119_, 6, v___x_117_);
lean_ctor_set(v___x_119_, 7, v___x_117_);
lean_ctor_set(v___x_119_, 8, v___x_117_);
lean_ctor_set(v___x_119_, 9, v___x_117_);
lean_ctor_set(v___x_119_, 10, v___x_117_);
lean_ctor_set(v___x_119_, 11, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(32u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_123_ = ((size_t)5ULL);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_unsigned_to_nat(32u);
v___x_126_ = lean_mk_empty_array_with_capacity(v___x_125_);
v___x_127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3);
v___x_128_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_124_);
lean_ctor_set(v___x_128_, 3, v___x_124_);
lean_ctor_set_usize(v___x_128_, 4, v___x_123_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_box(1);
v___x_130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4);
v___x_131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_129_);
return v___x_132_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(lean_object* v_msgData_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v_toCold_138_; lean_object* v_env_139_; lean_object* v_options_140_; uint8_t v___x_141_; lean_object* v_env_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_137_ = lean_st_ref_get(v___y_135_);
v_toCold_138_ = lean_ctor_get(v___y_134_, 0);
v_env_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_137_);
v_options_140_ = lean_ctor_get(v_toCold_138_, 2);
v___x_141_ = 0;
v_env_142_ = l_Lean_Environment_setRecordingDeps(v_env_139_, v___x_141_);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2);
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_140_);
v___x_145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_145_, 0, v_env_142_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_ctor_set(v___x_145_, 3, v_options_140_);
v___x_146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_msgData_133_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_133_ = stack[0].m_obj;
lean_object* v___y_134_ = stack[1].m_obj;
lean_object* v___y_135_ = stack[2].m_obj;
lean_object* v_res_148_;
v_res_148_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_153_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_162_, uint8_t v___y_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 1)
{
lean_object* v_pre_165_; 
v_pre_165_ = lean_ctor_get(v_x_164_, 0);
switch(lean_obj_tag(v_pre_165_))
{
case 1:
{
lean_object* v_pre_166_; 
v_pre_166_ = lean_ctor_get(v_pre_165_, 0);
switch(lean_obj_tag(v_pre_166_))
{
case 0:
{
lean_object* v_str_167_; lean_object* v_str_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_str_167_ = lean_ctor_get(v_x_164_, 1);
v_str_168_ = lean_ctor_get(v_pre_165_, 1);
v___x_169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_170_ = lean_string_dec_eq(v_str_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_172_ = lean_string_dec_eq(v_str_168_, v___x_171_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_174_ = lean_string_dec_eq(v_str_167_, v___x_173_);
if (v___x_174_ == 0)
{
return v___x_174_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_176_ = lean_string_dec_eq(v_str_167_, v___x_175_);
if (v___x_176_ == 0)
{
return v___x_176_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
case 1:
{
lean_object* v_pre_177_; 
v_pre_177_ = lean_ctor_get(v_pre_166_, 0);
if (lean_obj_tag(v_pre_177_) == 0)
{
lean_object* v_str_178_; lean_object* v_str_179_; lean_object* v_str_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_str_178_ = lean_ctor_get(v_x_164_, 1);
v_str_179_ = lean_ctor_get(v_pre_165_, 1);
v_str_180_ = lean_ctor_get(v_pre_166_, 1);
v___x_181_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_182_ = lean_string_dec_eq(v_str_180_, v___x_181_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_184_ = lean_string_dec_eq(v_str_179_, v___x_183_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6));
v___x_186_ = lean_string_dec_eq(v_str_178_, v___x_185_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
}
else
{
return v___y_163_;
}
}
default: 
{
return v___y_163_;
}
}
}
case 0:
{
lean_object* v_str_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_str_187_ = lean_ctor_get(v_x_164_, 1);
v___x_188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7));
v___x_189_ = lean_string_dec_eq(v_str_187_, v___x_188_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
return v_suppressElabErrors_162_;
}
}
default: 
{
return v___y_163_;
}
}
}
else
{
return v___y_163_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_162_ = stack[0].m_num;
uint8_t v___y_163_ = stack[1].m_num;
lean_object* v_x_164_ = stack[2].m_obj;
uint8_t v_res_190_;
v_res_190_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_162_, v___y_163_, v_x_164_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_191_, lean_object* v___y_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_suppressElabErrors_boxed_194_; uint8_t v___y_3795__boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_suppressElabErrors_boxed_194_ = lean_unbox(v_suppressElabErrors_191_);
v___y_3795__boxed_195_ = lean_unbox(v___y_192_);
v_res_196_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_194_, v___y_3795__boxed_195_, v_x_193_);
lean_dec(v_x_193_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(lean_object* v_ref_199_, lean_object* v_msgData_200_, uint8_t v_severity_201_, uint8_t v_isSilent_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___y_207_; lean_object* v___y_208_; uint8_t v___y_209_; uint8_t v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v_toCold_214_; lean_object* v___y_215_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; uint8_t v___y_247_; uint8_t v___y_248_; uint8_t v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; uint8_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; uint8_t v___y_281_; uint8_t v___y_282_; uint8_t v___y_283_; uint8_t v___x_294_; uint8_t v___y_296_; uint8_t v___y_297_; uint8_t v___y_298_; uint8_t v___y_300_; uint8_t v___x_308_; 
v___x_294_ = 2;
v___x_308_ = l_Lean_instBEqMessageSeverity_beq(v_severity_201_, v___x_294_);
if (v___x_308_ == 0)
{
v___y_300_ = v___x_308_;
goto v___jp_299_;
}
else
{
uint8_t v___x_309_; 
lean_inc_ref(v_msgData_200_);
v___x_309_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_200_);
v___y_300_ = v___x_309_;
goto v___jp_299_;
}
v___jp_206_:
{
lean_object* v_currNamespace_216_; lean_object* v_openDecls_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_env_222_; lean_object* v_nextMacroScope_223_; lean_object* v_ngen_224_; lean_object* v_auxDeclNGen_225_; lean_object* v_traceState_226_; lean_object* v_cache_227_; lean_object* v_recordedDeps_228_; lean_object* v_messages_229_; lean_object* v_infoState_230_; lean_object* v_snapshotTasks_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_242_; 
v_currNamespace_216_ = lean_ctor_get(v_toCold_214_, 4);
v_openDecls_217_ = lean_ctor_get(v_toCold_214_, 5);
lean_inc(v_openDecls_217_);
lean_inc(v_currNamespace_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_currNamespace_216_);
lean_ctor_set(v___x_218_, 1, v_openDecls_217_);
v___x_219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___y_211_);
lean_inc_ref(v___y_207_);
lean_inc_ref(v___y_212_);
v___x_220_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_220_, 0, v___y_212_);
lean_ctor_set(v___x_220_, 1, v___y_208_);
lean_ctor_set(v___x_220_, 2, v___y_213_);
lean_ctor_set(v___x_220_, 3, v___y_207_);
lean_ctor_set(v___x_220_, 4, v___x_219_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*5, v___y_210_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*5 + 1, v___y_209_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*5 + 2, v_isSilent_202_);
v___x_221_ = lean_st_ref_take(v___y_215_);
v_env_222_ = lean_ctor_get(v___x_221_, 0);
v_nextMacroScope_223_ = lean_ctor_get(v___x_221_, 1);
v_ngen_224_ = lean_ctor_get(v___x_221_, 2);
v_auxDeclNGen_225_ = lean_ctor_get(v___x_221_, 3);
v_traceState_226_ = lean_ctor_get(v___x_221_, 4);
v_cache_227_ = lean_ctor_get(v___x_221_, 5);
v_recordedDeps_228_ = lean_ctor_get(v___x_221_, 6);
v_messages_229_ = lean_ctor_get(v___x_221_, 7);
v_infoState_230_ = lean_ctor_get(v___x_221_, 8);
v_snapshotTasks_231_ = lean_ctor_get(v___x_221_, 9);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_242_ == 0)
{
v___x_233_ = v___x_221_;
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_snapshotTasks_231_);
lean_inc(v_infoState_230_);
lean_inc(v_messages_229_);
lean_inc(v_recordedDeps_228_);
lean_inc(v_cache_227_);
lean_inc(v_traceState_226_);
lean_inc(v_auxDeclNGen_225_);
lean_inc(v_ngen_224_);
lean_inc(v_nextMacroScope_223_);
lean_inc(v_env_222_);
lean_dec(v___x_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_235_ = lean_box(0);
v___x_236_ = l_Lean_MessageLog_add(v___x_220_, v_messages_229_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 7, v___x_236_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_env_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_nextMacroScope_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_ngen_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_auxDeclNGen_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_traceState_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_cache_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_recordedDeps_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v_infoState_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 9, v_snapshotTasks_231_);
v___x_238_ = v_reuseFailAlloc_241_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_st_ref_put(v___y_215_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_235_);
return v___x_240_;
}
}
}
v___jp_243_:
{
lean_object* v_fileName_252_; lean_object* v_fileMap_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_269_; 
v_fileName_252_ = lean_ctor_get(v___y_246_, 0);
v_fileMap_253_ = lean_ctor_get(v___y_246_, 1);
v___x_254_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_200_);
v___x_255_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v___x_254_, v___y_203_, v___y_204_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_269_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_269_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc_ref_n(v_fileMap_253_, 2);
v___x_260_ = l_Lean_FileMap_toPosition(v_fileMap_253_, v___y_250_);
lean_dec(v___y_250_);
v___x_261_ = l_Lean_FileMap_toPosition(v_fileMap_253_, v___y_251_);
lean_dec(v___y_251_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0));
if (v___y_247_ == 0)
{
lean_del_object(v___x_258_);
lean_dec_ref(v___y_245_);
v___y_207_ = v___x_263_;
v___y_208_ = v___x_260_;
v___y_209_ = v___y_248_;
v___y_210_ = v___y_249_;
v___y_211_ = v_a_256_;
v___y_212_ = v_fileName_252_;
v___y_213_ = v___x_262_;
v_toCold_214_ = v___y_244_;
v___y_215_ = v___y_204_;
goto v___jp_206_;
}
else
{
uint8_t v___x_264_; 
lean_inc(v_a_256_);
v___x_264_ = l_Lean_MessageData_hasTag(v___y_245_, v_a_256_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_267_; 
lean_dec_ref_known(v___x_262_, 1);
lean_dec_ref(v___x_260_);
lean_dec(v_a_256_);
v___x_265_ = lean_box(0);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_265_);
v___x_267_ = v___x_258_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_del_object(v___x_258_);
v___y_207_ = v___x_263_;
v___y_208_ = v___x_260_;
v___y_209_ = v___y_248_;
v___y_210_ = v___y_249_;
v___y_211_ = v_a_256_;
v___y_212_ = v_fileName_252_;
v___y_213_ = v___x_262_;
v_toCold_214_ = v___y_244_;
v___y_215_ = v___y_204_;
goto v___jp_206_;
}
}
}
}
v___jp_270_:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Syntax_getTailPos_x3f(v___y_276_, v___y_275_);
lean_dec(v___y_276_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_inc(v___y_277_);
v___y_244_ = v___y_271_;
v___y_245_ = v___y_273_;
v___y_246_ = v___y_271_;
v___y_247_ = v___y_272_;
v___y_248_ = v___y_274_;
v___y_249_ = v___y_275_;
v___y_250_ = v___y_277_;
v___y_251_ = v___y_277_;
goto v___jp_243_;
}
else
{
lean_object* v_val_279_; 
v_val_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_val_279_);
lean_dec_ref_known(v___x_278_, 1);
v___y_244_ = v___y_271_;
v___y_245_ = v___y_273_;
v___y_246_ = v___y_271_;
v___y_247_ = v___y_272_;
v___y_248_ = v___y_274_;
v___y_249_ = v___y_275_;
v___y_250_ = v___y_277_;
v___y_251_ = v_val_279_;
goto v___jp_243_;
}
}
v___jp_280_:
{
lean_object* v_toCold_284_; lean_object* v_ref_285_; uint8_t v_suppressElabErrors_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v_ref_290_; lean_object* v___x_291_; 
v_toCold_284_ = lean_ctor_get(v___y_203_, 0);
v_ref_285_ = lean_ctor_get(v___y_203_, 2);
v_suppressElabErrors_286_ = lean_ctor_get_uint8(v___y_203_, sizeof(void*)*3 + 2);
v___x_287_ = lean_box(v_suppressElabErrors_286_);
v___x_288_ = lean_box(v___y_281_);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_289_, 0, v___x_287_);
lean_closure_set(v___f_289_, 1, v___x_288_);
v_ref_290_ = l_Lean_replaceRef(v_ref_199_, v_ref_285_);
v___x_291_ = l_Lean_Syntax_getPos_x3f(v_ref_290_, v___y_282_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___y_271_ = v_toCold_284_;
v___y_272_ = v_suppressElabErrors_286_;
v___y_273_ = v___f_289_;
v___y_274_ = v___y_283_;
v___y_275_ = v___y_282_;
v___y_276_ = v_ref_290_;
v___y_277_ = v___x_292_;
goto v___jp_270_;
}
else
{
lean_object* v_val_293_; 
v_val_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_293_);
lean_dec_ref_known(v___x_291_, 1);
v___y_271_ = v_toCold_284_;
v___y_272_ = v_suppressElabErrors_286_;
v___y_273_ = v___f_289_;
v___y_274_ = v___y_283_;
v___y_275_ = v___y_282_;
v___y_276_ = v_ref_290_;
v___y_277_ = v_val_293_;
goto v___jp_270_;
}
}
v___jp_295_:
{
if (v___y_298_ == 0)
{
v___y_281_ = v___y_296_;
v___y_282_ = v___y_297_;
v___y_283_ = v_severity_201_;
goto v___jp_280_;
}
else
{
v___y_281_ = v___y_296_;
v___y_282_ = v___y_297_;
v___y_283_ = v___x_294_;
goto v___jp_280_;
}
}
v___jp_299_:
{
if (v___y_300_ == 0)
{
uint8_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 1;
v___x_302_ = l_Lean_instBEqMessageSeverity_beq(v_severity_201_, v___x_301_);
if (v___x_302_ == 0)
{
v___y_296_ = v___y_300_;
v___y_297_ = v___y_300_;
v___y_298_ = v___x_302_;
goto v___jp_295_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_203_);
v___x_304_ = l_Lean_warningAsError;
v___x_305_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v___x_303_, v___x_304_);
lean_dec_ref(v___x_303_);
v___y_296_ = v___y_300_;
v___y_297_ = v___y_300_;
v___y_298_ = v___x_305_;
goto v___jp_295_;
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v_msgData_200_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_199_ = stack[0].m_obj;
lean_object* v_msgData_200_ = stack[1].m_obj;
uint8_t v_severity_201_ = stack[2].m_num;
uint8_t v_isSilent_202_ = stack[3].m_num;
lean_object* v___y_203_ = stack[4].m_obj;
lean_object* v___y_204_ = stack[5].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_199_, v_msgData_200_, v_severity_201_, v_isSilent_202_, v___y_203_, v___y_204_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_311_, lean_object* v_msgData_312_, lean_object* v_severity_313_, lean_object* v_isSilent_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
uint8_t v_severity_boxed_318_; uint8_t v_isSilent_boxed_319_; lean_object* v_res_320_; 
v_severity_boxed_318_ = lean_unbox(v_severity_313_);
v_isSilent_boxed_319_ = lean_unbox(v_isSilent_314_);
v_res_320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_311_, v_msgData_312_, v_severity_boxed_318_, v_isSilent_boxed_319_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v_ref_311_);
return v_res_320_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(lean_object* v_msgData_321_, uint8_t v_severity_322_, uint8_t v_isSilent_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_ref_327_; lean_object* v___x_328_; 
v_ref_327_ = lean_ctor_get(v___y_324_, 2);
v___x_328_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_327_, v_msgData_321_, v_severity_322_, v_isSilent_323_, v___y_324_, v___y_325_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_321_ = stack[0].m_obj;
uint8_t v_severity_322_ = stack[1].m_num;
uint8_t v_isSilent_323_ = stack[2].m_num;
lean_object* v___y_324_ = stack[3].m_obj;
lean_object* v___y_325_ = stack[4].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_321_, v_severity_322_, v_isSilent_323_, v___y_324_, v___y_325_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(lean_object* v_msgData_330_, lean_object* v_severity_331_, lean_object* v_isSilent_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v_severity_boxed_336_; uint8_t v_isSilent_boxed_337_; lean_object* v_res_338_; 
v_severity_boxed_336_ = lean_unbox(v_severity_331_);
v_isSilent_boxed_337_ = lean_unbox(v_isSilent_332_);
v_res_338_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_330_, v_severity_boxed_336_, v_isSilent_boxed_337_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = 1;
v___x_344_ = 0;
v___x_345_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_339_, v___x_343_, v___x_344_, v___y_340_, v___y_341_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkExponent_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_339_ = stack[0].m_obj;
lean_object* v___y_340_ = stack[1].m_obj;
lean_object* v___y_341_ = stack[2].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v_msgData_339_, v___y_340_, v___y_341_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
lean_object* l_Lean_checkExponent(lean_object* v_n_360_, uint8_t v_warning_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_exponentiation_threshold;
v___x_370_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v___x_369_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_417_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_417_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_417_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_417_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_lt(v_a_371_, v_n_360_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec(v_a_371_);
lean_dec(v_n_360_);
v___x_376_ = 1;
v___x_377_ = lean_box(v___x_376_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_377_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_del_object(v___x_373_);
if (v_warning_361_ == 0)
{
lean_dec(v_a_371_);
lean_dec(v_n_360_);
goto v___jp_365_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_checkExponent___closed__1));
v___x_382_ = l_Lean_logMessageKind___redArg(v___x_381_, v_a_363_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_416_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_416_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_416_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_416_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v_a_383_);
if (v___x_387_ == 0)
{
lean_del_object(v___x_385_);
lean_dec(v_a_383_);
lean_dec(v_a_371_);
lean_dec(v_n_360_);
goto v___jp_365_;
}
else
{
lean_object* v_name_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_name_388_ = lean_ctor_get(v___x_369_, 0);
v___x_389_ = ((lean_object*)(l_Lean_checkExponent___closed__2));
v___x_390_ = l_Nat_reprFast(v_n_360_);
v___x_391_ = lean_string_append(v___x_389_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = ((lean_object*)(l_Lean_checkExponent___closed__3));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = l_Nat_reprFast(v_a_371_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = ((lean_object*)(l_Lean_checkExponent___closed__4));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
v___x_398_ = lean_unbox(v_a_383_);
lean_dec(v_a_383_);
lean_inc(v_name_388_);
v___x_399_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_388_, v___x_398_);
v___x_400_ = lean_string_append(v___x_397_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l_Lean_checkExponent___closed__5));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 3);
lean_ctor_set(v___x_385_, 0, v___x_402_);
v___x_404_ = v___x_385_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_415_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = l_Lean_MessageData_ofFormat(v___x_404_);
v___x_406_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v___x_405_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec_ref_known(v___x_406_, 1);
goto v___jp_365_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_371_);
lean_dec(v_n_360_);
return v___x_382_;
}
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_n_360_);
v_a_418_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_370_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_370_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
v___jp_365_:
{
uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = 0;
v___x_367_ = lean_box(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT void l_Lean_checkExponent_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_360_ = stack[0].m_obj;
uint8_t v_warning_361_ = stack[1].m_num;
lean_object* v_a_362_ = stack[2].m_obj;
lean_object* v_a_363_ = stack[3].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_checkExponent(v_n_360_, v_warning_361_, v_a_362_, v_a_363_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object* v_n_427_, lean_object* v_warning_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_warning_boxed_432_; lean_object* v_res_433_; 
v_warning_boxed_432_ = lean_unbox(v_warning_428_);
v_res_433_ = l_Lean_checkExponent(v_n_427_, v_warning_boxed_432_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_433_;
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
