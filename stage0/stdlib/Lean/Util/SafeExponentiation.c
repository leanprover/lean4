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
lean_object* l___private_Lean_CoreM_0__Lean_recordOptionAccess(lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_59_; lean_object* v_options_60_; lean_object* v_name_61_; lean_object* v_defValue_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_96_; 
v_toCold_59_ = lean_ctor_get(v_a_56_, 0);
v_options_60_ = lean_ctor_get(v_toCold_59_, 2);
v_name_61_ = lean_ctor_get(v_opt_55_, 0);
v_defValue_62_ = lean_ctor_get(v_opt_55_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_opt_55_);
if (v_isSharedCheck_96_ == 0)
{
v___x_64_ = v_opt_55_;
v_isShared_65_ = v_isSharedCheck_96_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_defValue_62_);
lean_inc(v_name_61_);
lean_dec(v_opt_55_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_96_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_map_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v_map_66_ = lean_ctor_get(v_options_60_, 0);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_66_, v_name_61_);
lean_inc(v___x_67_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_name_61_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_95_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; 
v___x_70_ = l___private_Lean_CoreM_0__Lean_recordOptionAccess(v___x_69_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_85_; 
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v___x_70_, 0);
lean_dec(v_unused_86_);
v___x_72_ = v___x_70_;
v_isShared_73_ = v_isSharedCheck_85_;
goto v_resetjp_71_;
}
else
{
lean_dec(v___x_70_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_85_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_defValue_62_);
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_defValue_62_);
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
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_67_, 1);
if (lean_obj_tag(v_val_77_) == 3)
{
lean_object* v_v_78_; lean_object* v___x_80_; 
lean_dec(v_defValue_62_);
v_v_78_ = lean_ctor_get(v_val_77_, 0);
lean_inc(v_v_78_);
lean_dec_ref_known(v_val_77_, 1);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_v_78_);
v___x_80_ = v___x_72_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_v_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v___x_83_; 
lean_dec(v_val_77_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_defValue_62_);
v___x_83_ = v___x_72_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_defValue_62_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec(v___x_67_);
lean_dec(v_defValue_62_);
v_a_87_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_70_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_70_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0___boxed(lean_object* v_opt_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v_opt_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_102_, lean_object* v_opt_103_){
_start:
{
lean_object* v_name_104_; lean_object* v_defValue_105_; lean_object* v_map_106_; lean_object* v___x_107_; 
v_name_104_ = lean_ctor_get(v_opt_103_, 0);
v_defValue_105_ = lean_ctor_get(v_opt_103_, 1);
v_map_106_ = lean_ctor_get(v_opts_102_, 0);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_106_, v_name_104_);
if (lean_obj_tag(v___x_107_) == 0)
{
uint8_t v___x_108_; 
v___x_108_ = lean_unbox(v_defValue_105_);
return v___x_108_;
}
else
{
lean_object* v_val_109_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_107_, 1);
if (lean_obj_tag(v_val_109_) == 1)
{
uint8_t v_v_110_; 
v_v_110_ = lean_ctor_get_uint8(v_val_109_, 0);
lean_dec_ref_known(v_val_109_, 0);
return v_v_110_;
}
else
{
uint8_t v___x_111_; 
lean_dec(v_val_109_);
v___x_111_ = lean_unbox(v_defValue_105_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_112_, lean_object* v_opt_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_112_, v_opt_113_);
lean_dec_ref(v_opt_113_);
lean_dec_ref(v_opts_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_116_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
lean_ctor_set(v___x_121_, 4, v___x_119_);
lean_ctor_set(v___x_121_, 5, v___x_119_);
lean_ctor_set(v___x_121_, 6, v___x_119_);
lean_ctor_set(v___x_121_, 7, v___x_119_);
lean_ctor_set(v___x_121_, 8, v___x_119_);
lean_ctor_set(v___x_121_, 9, v___x_119_);
lean_ctor_set(v___x_121_, 10, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(32u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_unsigned_to_nat(32u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3);
v___x_130_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_126_);
lean_ctor_set(v___x_130_, 3, v___x_126_);
lean_ctor_set_usize(v___x_130_, 4, v___x_125_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = lean_box(1);
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(lean_object* v_msgData_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v_toCold_140_; lean_object* v_env_141_; lean_object* v_options_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v_toCold_140_ = lean_ctor_get(v___y_136_, 0);
v_env_141_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_env_141_);
lean_dec(v___x_139_);
v_options_142_ = lean_ctor_get(v_toCold_140_, 2);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2);
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_142_);
v___x_145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_145_, 0, v_env_141_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_ctor_set(v___x_145_, 3, v_options_142_);
v___x_146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_msgData_135_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_msgData_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_161_, uint8_t v___y_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 1)
{
lean_object* v_pre_164_; 
v_pre_164_ = lean_ctor_get(v_x_163_, 0);
switch(lean_obj_tag(v_pre_164_))
{
case 1:
{
lean_object* v_pre_165_; 
v_pre_165_ = lean_ctor_get(v_pre_164_, 0);
switch(lean_obj_tag(v_pre_165_))
{
case 0:
{
lean_object* v_str_166_; lean_object* v_str_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_166_ = lean_ctor_get(v_x_163_, 1);
v_str_167_ = lean_ctor_get(v_pre_164_, 1);
v___x_168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_169_ = lean_string_dec_eq(v_str_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_171_ = lean_string_dec_eq(v_str_167_, v___x_170_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_173_ = lean_string_dec_eq(v_str_166_, v___x_172_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
return v_suppressElabErrors_161_;
}
}
}
else
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_175_ = lean_string_dec_eq(v_str_166_, v___x_174_);
if (v___x_175_ == 0)
{
return v___x_175_;
}
else
{
return v_suppressElabErrors_161_;
}
}
}
case 1:
{
lean_object* v_pre_176_; 
v_pre_176_ = lean_ctor_get(v_pre_165_, 0);
if (lean_obj_tag(v_pre_176_) == 0)
{
lean_object* v_str_177_; lean_object* v_str_178_; lean_object* v_str_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_str_177_ = lean_ctor_get(v_x_163_, 1);
v_str_178_ = lean_ctor_get(v_pre_164_, 1);
v_str_179_ = lean_ctor_get(v_pre_165_, 1);
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_181_ = lean_string_dec_eq(v_str_179_, v___x_180_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_183_ = lean_string_dec_eq(v_str_178_, v___x_182_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6));
v___x_185_ = lean_string_dec_eq(v_str_177_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
return v_suppressElabErrors_161_;
}
}
}
}
else
{
return v___y_162_;
}
}
default: 
{
return v___y_162_;
}
}
}
case 0:
{
lean_object* v_str_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_str_186_ = lean_ctor_get(v_x_163_, 1);
v___x_187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7));
v___x_188_ = lean_string_dec_eq(v_str_186_, v___x_187_);
if (v___x_188_ == 0)
{
return v___x_188_;
}
else
{
return v_suppressElabErrors_161_;
}
}
default: 
{
return v___y_162_;
}
}
}
else
{
return v___y_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_189_, lean_object* v___y_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_suppressElabErrors_boxed_192_; uint8_t v___y_3728__boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_suppressElabErrors_boxed_192_ = lean_unbox(v_suppressElabErrors_189_);
v___y_3728__boxed_193_ = lean_unbox(v___y_190_);
v_res_194_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_192_, v___y_3728__boxed_193_, v_x_191_);
lean_dec(v_x_191_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(lean_object* v_ref_197_, lean_object* v_msgData_198_, uint8_t v_severity_199_, uint8_t v_isSilent_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___y_205_; lean_object* v___y_206_; uint8_t v___y_207_; lean_object* v___y_208_; uint8_t v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v_toCold_212_; lean_object* v___y_213_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; uint8_t v___y_246_; uint8_t v___y_247_; uint8_t v___y_248_; lean_object* v___y_249_; lean_object* v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; uint8_t v___y_272_; uint8_t v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; uint8_t v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; uint8_t v___x_292_; uint8_t v___y_294_; uint8_t v___y_295_; uint8_t v___y_296_; uint8_t v___y_298_; uint8_t v___x_306_; 
v___x_292_ = 2;
v___x_306_ = l_Lean_instBEqMessageSeverity_beq(v_severity_199_, v___x_292_);
if (v___x_306_ == 0)
{
v___y_298_ = v___x_306_;
goto v___jp_297_;
}
else
{
uint8_t v___x_307_; 
lean_inc_ref(v_msgData_198_);
v___x_307_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_198_);
v___y_298_ = v___x_307_;
goto v___jp_297_;
}
v___jp_204_:
{
lean_object* v_currNamespace_214_; lean_object* v_openDecls_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_env_220_; lean_object* v_nextMacroScope_221_; lean_object* v_ngen_222_; lean_object* v_auxDeclNGen_223_; lean_object* v_traceState_224_; lean_object* v_cache_225_; lean_object* v_recordedDeps_226_; lean_object* v_messages_227_; lean_object* v_infoState_228_; lean_object* v_snapshotTasks_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_240_; 
v_currNamespace_214_ = lean_ctor_get(v_toCold_212_, 4);
v_openDecls_215_ = lean_ctor_get(v_toCold_212_, 5);
lean_inc(v_openDecls_215_);
lean_inc(v_currNamespace_214_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_currNamespace_214_);
lean_ctor_set(v___x_216_, 1, v_openDecls_215_);
v___x_217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___y_208_);
lean_inc_ref(v___y_206_);
lean_inc_ref(v___y_205_);
v___x_218_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_218_, 0, v___y_205_);
lean_ctor_set(v___x_218_, 1, v___y_211_);
lean_ctor_set(v___x_218_, 2, v___y_210_);
lean_ctor_set(v___x_218_, 3, v___y_206_);
lean_ctor_set(v___x_218_, 4, v___x_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5, v___y_209_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5 + 1, v___y_207_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5 + 2, v_isSilent_200_);
v___x_219_ = lean_st_ref_take(v___y_213_);
v_env_220_ = lean_ctor_get(v___x_219_, 0);
v_nextMacroScope_221_ = lean_ctor_get(v___x_219_, 1);
v_ngen_222_ = lean_ctor_get(v___x_219_, 2);
v_auxDeclNGen_223_ = lean_ctor_get(v___x_219_, 3);
v_traceState_224_ = lean_ctor_get(v___x_219_, 4);
v_cache_225_ = lean_ctor_get(v___x_219_, 5);
v_recordedDeps_226_ = lean_ctor_get(v___x_219_, 6);
v_messages_227_ = lean_ctor_get(v___x_219_, 7);
v_infoState_228_ = lean_ctor_get(v___x_219_, 8);
v_snapshotTasks_229_ = lean_ctor_get(v___x_219_, 9);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_240_ == 0)
{
v___x_231_ = v___x_219_;
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snapshotTasks_229_);
lean_inc(v_infoState_228_);
lean_inc(v_messages_227_);
lean_inc(v_recordedDeps_226_);
lean_inc(v_cache_225_);
lean_inc(v_traceState_224_);
lean_inc(v_auxDeclNGen_223_);
lean_inc(v_ngen_222_);
lean_inc(v_nextMacroScope_221_);
lean_inc(v_env_220_);
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_box(0);
v___x_234_ = l_Lean_MessageLog_add(v___x_218_, v_messages_227_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 7, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_env_220_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_nextMacroScope_221_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_ngen_222_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_auxDeclNGen_223_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_traceState_224_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v_cache_225_);
lean_ctor_set(v_reuseFailAlloc_239_, 6, v_recordedDeps_226_);
lean_ctor_set(v_reuseFailAlloc_239_, 7, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_239_, 8, v_infoState_228_);
lean_ctor_set(v_reuseFailAlloc_239_, 9, v_snapshotTasks_229_);
v___x_236_ = v_reuseFailAlloc_239_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_st_ref_put(v___y_213_, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
return v___x_238_;
}
}
}
v___jp_241_:
{
lean_object* v_fileName_250_; lean_object* v_fileMap_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_267_; 
v_fileName_250_ = lean_ctor_get(v___y_245_, 0);
v_fileMap_251_ = lean_ctor_get(v___y_245_, 1);
v___x_252_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_198_);
v___x_253_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v___x_252_, v___y_201_, v___y_202_);
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_267_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_267_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_267_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc_ref_n(v_fileMap_251_, 2);
v___x_258_ = l_Lean_FileMap_toPosition(v_fileMap_251_, v___y_244_);
lean_dec(v___y_244_);
v___x_259_ = l_Lean_FileMap_toPosition(v_fileMap_251_, v___y_249_);
lean_dec(v___y_249_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0));
if (v___y_246_ == 0)
{
lean_del_object(v___x_256_);
lean_dec_ref(v___y_242_);
v___y_205_ = v_fileName_250_;
v___y_206_ = v___x_261_;
v___y_207_ = v___y_247_;
v___y_208_ = v_a_254_;
v___y_209_ = v___y_248_;
v___y_210_ = v___x_260_;
v___y_211_ = v___x_258_;
v_toCold_212_ = v___y_243_;
v___y_213_ = v___y_202_;
goto v___jp_204_;
}
else
{
uint8_t v___x_262_; 
lean_inc(v_a_254_);
v___x_262_ = l_Lean_MessageData_hasTag(v___y_242_, v_a_254_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec_ref_known(v___x_260_, 1);
lean_dec_ref(v___x_258_);
lean_dec(v_a_254_);
v___x_263_ = lean_box(0);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_263_);
v___x_265_ = v___x_256_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_del_object(v___x_256_);
v___y_205_ = v_fileName_250_;
v___y_206_ = v___x_261_;
v___y_207_ = v___y_247_;
v___y_208_ = v_a_254_;
v___y_209_ = v___y_248_;
v___y_210_ = v___x_260_;
v___y_211_ = v___x_258_;
v_toCold_212_ = v___y_243_;
v___y_213_ = v___y_202_;
goto v___jp_204_;
}
}
}
}
v___jp_268_:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Syntax_getTailPos_x3f(v___y_274_, v___y_273_);
lean_dec(v___y_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_inc(v___y_275_);
v___y_242_ = v___y_269_;
v___y_243_ = v___y_270_;
v___y_244_ = v___y_275_;
v___y_245_ = v___y_270_;
v___y_246_ = v___y_271_;
v___y_247_ = v___y_272_;
v___y_248_ = v___y_273_;
v___y_249_ = v___y_275_;
goto v___jp_241_;
}
else
{
lean_object* v_val_277_; 
v_val_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_276_, 1);
v___y_242_ = v___y_269_;
v___y_243_ = v___y_270_;
v___y_244_ = v___y_275_;
v___y_245_ = v___y_270_;
v___y_246_ = v___y_271_;
v___y_247_ = v___y_272_;
v___y_248_ = v___y_273_;
v___y_249_ = v_val_277_;
goto v___jp_241_;
}
}
v___jp_278_:
{
lean_object* v_toCold_282_; lean_object* v_ref_283_; uint8_t v_suppressElabErrors_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v_ref_288_; lean_object* v___x_289_; 
v_toCold_282_ = lean_ctor_get(v___y_201_, 0);
v_ref_283_ = lean_ctor_get(v___y_201_, 2);
v_suppressElabErrors_284_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*3 + 2);
v___x_285_ = lean_box(v_suppressElabErrors_284_);
v___x_286_ = lean_box(v___y_279_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_287_, 0, v___x_285_);
lean_closure_set(v___f_287_, 1, v___x_286_);
v_ref_288_ = l_Lean_replaceRef(v_ref_197_, v_ref_283_);
v___x_289_ = l_Lean_Syntax_getPos_x3f(v_ref_288_, v___y_280_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___y_269_ = v___f_287_;
v___y_270_ = v_toCold_282_;
v___y_271_ = v_suppressElabErrors_284_;
v___y_272_ = v___y_281_;
v___y_273_ = v___y_280_;
v___y_274_ = v_ref_288_;
v___y_275_ = v___x_290_;
goto v___jp_268_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_289_, 1);
v___y_269_ = v___f_287_;
v___y_270_ = v_toCold_282_;
v___y_271_ = v_suppressElabErrors_284_;
v___y_272_ = v___y_281_;
v___y_273_ = v___y_280_;
v___y_274_ = v_ref_288_;
v___y_275_ = v_val_291_;
goto v___jp_268_;
}
}
v___jp_293_:
{
if (v___y_296_ == 0)
{
v___y_279_ = v___y_294_;
v___y_280_ = v___y_295_;
v___y_281_ = v_severity_199_;
goto v___jp_278_;
}
else
{
v___y_279_ = v___y_294_;
v___y_280_ = v___y_295_;
v___y_281_ = v___x_292_;
goto v___jp_278_;
}
}
v___jp_297_:
{
if (v___y_298_ == 0)
{
uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 1;
v___x_300_ = l_Lean_instBEqMessageSeverity_beq(v_severity_199_, v___x_299_);
if (v___x_300_ == 0)
{
v___y_294_ = v___y_298_;
v___y_295_ = v___y_298_;
v___y_296_ = v___x_300_;
goto v___jp_293_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_201_);
v___x_302_ = l_Lean_warningAsError;
v___x_303_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v___x_301_, v___x_302_);
lean_dec_ref(v___x_301_);
v___y_294_ = v___y_298_;
v___y_295_ = v___y_298_;
v___y_296_ = v___x_303_;
goto v___jp_293_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_msgData_198_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_308_, lean_object* v_msgData_309_, lean_object* v_severity_310_, lean_object* v_isSilent_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v_severity_boxed_315_; uint8_t v_isSilent_boxed_316_; lean_object* v_res_317_; 
v_severity_boxed_315_ = lean_unbox(v_severity_310_);
v_isSilent_boxed_316_ = lean_unbox(v_isSilent_311_);
v_res_317_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_308_, v_msgData_309_, v_severity_boxed_315_, v_isSilent_boxed_316_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v_ref_308_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(lean_object* v_msgData_318_, uint8_t v_severity_319_, uint8_t v_isSilent_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_ref_324_; lean_object* v___x_325_; 
v_ref_324_ = lean_ctor_get(v___y_321_, 2);
v___x_325_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_324_, v_msgData_318_, v_severity_319_, v_isSilent_320_, v___y_321_, v___y_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(lean_object* v_msgData_326_, lean_object* v_severity_327_, lean_object* v_isSilent_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
uint8_t v_severity_boxed_332_; uint8_t v_isSilent_boxed_333_; lean_object* v_res_334_; 
v_severity_boxed_332_ = lean_unbox(v_severity_327_);
v_isSilent_boxed_333_ = lean_unbox(v_isSilent_328_);
v_res_334_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_326_, v_severity_boxed_332_, v_isSilent_boxed_333_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = 1;
v___x_340_ = 0;
v___x_341_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_335_, v___x_339_, v___x_340_, v___y_336_, v___y_337_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v_msgData_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object* v_n_355_, uint8_t v_warning_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_exponentiation_threshold;
v___x_365_ = l_Lean_getRecordedOption___at___00Lean_checkExponent_spec__0(v___x_364_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_412_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_412_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_412_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_412_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; 
v___x_370_ = lean_nat_dec_lt(v_a_366_, v_n_355_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec(v_a_366_);
lean_dec(v_n_355_);
v___x_371_ = 1;
v___x_372_ = lean_box(v___x_371_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_372_);
v___x_374_ = v___x_368_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_del_object(v___x_368_);
if (v_warning_356_ == 0)
{
lean_dec(v_a_366_);
lean_dec(v_n_355_);
goto v___jp_360_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_checkExponent___closed__1));
v___x_377_ = l_Lean_logMessageKind___redArg(v___x_376_, v_a_358_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_411_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_411_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_411_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_411_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v_a_378_);
if (v___x_382_ == 0)
{
lean_del_object(v___x_380_);
lean_dec(v_a_378_);
lean_dec(v_a_366_);
lean_dec(v_n_355_);
goto v___jp_360_;
}
else
{
lean_object* v_name_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v_name_383_ = lean_ctor_get(v___x_364_, 0);
v___x_384_ = ((lean_object*)(l_Lean_checkExponent___closed__2));
v___x_385_ = l_Nat_reprFast(v_n_355_);
v___x_386_ = lean_string_append(v___x_384_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_checkExponent___closed__3));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = l_Nat_reprFast(v_a_366_);
v___x_390_ = lean_string_append(v___x_388_, v___x_389_);
lean_dec_ref(v___x_389_);
v___x_391_ = ((lean_object*)(l_Lean_checkExponent___closed__4));
v___x_392_ = lean_string_append(v___x_390_, v___x_391_);
v___x_393_ = lean_unbox(v_a_378_);
lean_dec(v_a_378_);
lean_inc(v_name_383_);
v___x_394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_383_, v___x_393_);
v___x_395_ = lean_string_append(v___x_392_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = ((lean_object*)(l_Lean_checkExponent___closed__5));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 3);
lean_ctor_set(v___x_380_, 0, v___x_397_);
v___x_399_ = v___x_380_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_410_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = l_Lean_MessageData_ofFormat(v___x_399_);
v___x_401_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v___x_400_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_dec_ref_known(v___x_401_, 1);
goto v___jp_360_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_366_);
lean_dec(v_n_355_);
return v___x_377_;
}
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_n_355_);
v_a_413_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_365_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_365_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
v___jp_360_:
{
uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = 0;
v___x_362_ = lean_box(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object* v_n_421_, lean_object* v_warning_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
uint8_t v_warning_boxed_426_; lean_object* v_res_427_; 
v_warning_boxed_426_ = lean_unbox(v_warning_422_);
v_res_427_ = l_Lean_checkExponent(v_n_421_, v_warning_boxed_426_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_427_;
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
