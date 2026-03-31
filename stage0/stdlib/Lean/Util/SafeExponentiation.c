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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "exponentiation"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(83, 126, 177, 93, 34, 88, 85, 55)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 127, 45, 106, 162, 118, 90, 191)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 300, .m_capacity = 300, .m_length = 299, .m_data = "maximum value for which exponentiation operations are safe to evaluate. When an exponent is a value greater than this threshold, the exponentiation will not be evaluated, and a warning will be logged. This helps to prevent the system from becoming unresponsive due to excessively large computations."};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(66, 195, 247, 99, 191, 194, 19, 186)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 37, 3, 64, 108, 254, 216, 252)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exponentiation_threshold;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_checkExponent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_checkExponent_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_checkExponent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_checkExponent___closed__1_value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(50, 3, 22, 131, 26, 69, 126, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_32_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_32_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_defValue_5_);
v___x_10_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_10_, 0, v_defValue_5_);
lean_inc_n(v_name_1_, 2);
v___x_11_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_11_, 0, v_name_1_);
lean_ctor_set(v___x_11_, 1, v_ref_3_);
lean_ctor_set(v___x_11_, 2, v___x_10_);
lean_ctor_set(v___x_11_, 3, v_descr_6_);
v___x_12_ = lean_register_option(v_name_1_, v___x_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_22_; 
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_23_);
v___x_14_ = v___x_12_;
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
else
{
lean_dec(v___x_12_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_17_ = v___x_8_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_defValue_5_);
v___x_17_ = v_reuseFailAlloc_21_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_19_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_17_);
v___x_19_ = v___x_14_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_24_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_12_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_12_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_33_, lean_object* v_decl_34_, lean_object* v_ref_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v_name_33_, v_decl_34_, v_ref_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_checkExponent_spec__0(lean_object* v_opts_59_, lean_object* v_opt_60_){
_start:
{
lean_object* v_name_61_; lean_object* v_defValue_62_; lean_object* v_map_63_; lean_object* v___x_64_; 
v_name_61_ = lean_ctor_get(v_opt_60_, 0);
v_defValue_62_ = lean_ctor_get(v_opt_60_, 1);
v_map_63_ = lean_ctor_get(v_opts_59_, 0);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_63_, v_name_61_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_inc(v_defValue_62_);
return v_defValue_62_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_val_65_);
lean_dec_ref(v___x_64_);
if (lean_obj_tag(v_val_65_) == 3)
{
lean_object* v_v_66_; 
v_v_66_ = lean_ctor_get(v_val_65_, 0);
lean_inc(v_v_66_);
lean_dec_ref(v_val_65_);
return v_v_66_;
}
else
{
lean_dec(v_val_65_);
lean_inc(v_defValue_62_);
return v_defValue_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_checkExponent_spec__0___boxed(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Option_get___at___00Lean_checkExponent_spec__0(v_opts_67_, v_opt_68_);
lean_dec_ref(v_opt_68_);
lean_dec_ref(v_opts_67_);
return v_res_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_70_, lean_object* v_opt_71_){
_start:
{
lean_object* v_name_72_; lean_object* v_defValue_73_; lean_object* v_map_74_; lean_object* v___x_75_; 
v_name_72_ = lean_ctor_get(v_opt_71_, 0);
v_defValue_73_ = lean_ctor_get(v_opt_71_, 1);
v_map_74_ = lean_ctor_get(v_opts_70_, 0);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_74_, v_name_72_);
if (lean_obj_tag(v___x_75_) == 0)
{
uint8_t v___x_76_; 
v___x_76_ = lean_unbox(v_defValue_73_);
return v___x_76_;
}
else
{
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_77_);
lean_dec_ref(v___x_75_);
if (lean_obj_tag(v_val_77_) == 1)
{
uint8_t v_v_78_; 
v_v_78_ = lean_ctor_get_uint8(v_val_77_, 0);
lean_dec_ref(v_val_77_);
return v_v_78_;
}
else
{
uint8_t v___x_79_; 
lean_dec(v_val_77_);
v___x_79_ = lean_unbox(v_defValue_73_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_80_, lean_object* v_opt_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_80_, v_opt_81_);
lean_dec_ref(v_opt_81_);
lean_dec_ref(v_opts_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_84_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
lean_ctor_set(v___x_89_, 3, v___x_87_);
lean_ctor_set(v___x_89_, 4, v___x_87_);
lean_ctor_set(v___x_89_, 5, v___x_87_);
lean_ctor_set(v___x_89_, 6, v___x_87_);
lean_ctor_set(v___x_89_, 7, v___x_87_);
lean_ctor_set(v___x_89_, 8, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(32u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3);
v___x_98_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_94_);
lean_ctor_set(v___x_98_, 3, v___x_94_);
lean_ctor_set_usize(v___x_98_, 4, v___x_93_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_box(1);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4);
v___x_101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v_options_109_ = lean_ctor_get(v___y_104_, 2);
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2);
v___x_111_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_109_);
v___x_112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_112_, 0, v_env_108_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
lean_ctor_set(v___x_112_, 2, v___x_111_);
lean_ctor_set(v___x_112_, 3, v_options_109_);
v___x_113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_msgData_103_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_msgData_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_119_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_128_, uint8_t v_suppressElabErrors_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 1)
{
lean_object* v_pre_131_; 
v_pre_131_ = lean_ctor_get(v_x_130_, 0);
switch(lean_obj_tag(v_pre_131_))
{
case 1:
{
lean_object* v_pre_132_; 
v_pre_132_ = lean_ctor_get(v_pre_131_, 0);
switch(lean_obj_tag(v_pre_132_))
{
case 0:
{
lean_object* v_str_133_; lean_object* v_str_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_str_133_ = lean_ctor_get(v_x_130_, 1);
v_str_134_ = lean_ctor_get(v_pre_131_, 1);
v___x_135_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_136_ = lean_string_dec_eq(v_str_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_138_ = lean_string_dec_eq(v_str_134_, v___x_137_);
if (v___x_138_ == 0)
{
return v___y_128_;
}
else
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_140_ = lean_string_dec_eq(v_str_133_, v___x_139_);
if (v___x_140_ == 0)
{
return v___y_128_;
}
else
{
return v_suppressElabErrors_129_;
}
}
}
else
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_142_ = lean_string_dec_eq(v_str_133_, v___x_141_);
if (v___x_142_ == 0)
{
return v___y_128_;
}
else
{
return v_suppressElabErrors_129_;
}
}
}
case 1:
{
lean_object* v_pre_143_; 
v_pre_143_ = lean_ctor_get(v_pre_132_, 0);
if (lean_obj_tag(v_pre_143_) == 0)
{
lean_object* v_str_144_; lean_object* v_str_145_; lean_object* v_str_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_str_144_ = lean_ctor_get(v_x_130_, 1);
v_str_145_ = lean_ctor_get(v_pre_131_, 1);
v_str_146_ = lean_ctor_get(v_pre_132_, 1);
v___x_147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_148_ = lean_string_dec_eq(v_str_146_, v___x_147_);
if (v___x_148_ == 0)
{
return v___y_128_;
}
else
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_150_ = lean_string_dec_eq(v_str_145_, v___x_149_);
if (v___x_150_ == 0)
{
return v___y_128_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6));
v___x_152_ = lean_string_dec_eq(v_str_144_, v___x_151_);
if (v___x_152_ == 0)
{
return v___y_128_;
}
else
{
return v_suppressElabErrors_129_;
}
}
}
}
else
{
return v___y_128_;
}
}
default: 
{
return v___y_128_;
}
}
}
case 0:
{
lean_object* v_str_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_str_153_ = lean_ctor_get(v_x_130_, 1);
v___x_154_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7));
v___x_155_ = lean_string_dec_eq(v_str_153_, v___x_154_);
if (v___x_155_ == 0)
{
return v___y_128_;
}
else
{
return v_suppressElabErrors_129_;
}
}
default: 
{
return v___y_128_;
}
}
}
else
{
return v___y_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_156_, lean_object* v_suppressElabErrors_157_, lean_object* v_x_158_){
_start:
{
uint8_t v___y_3443__boxed_159_; uint8_t v_suppressElabErrors_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v___y_3443__boxed_159_ = lean_unbox(v___y_156_);
v_suppressElabErrors_boxed_160_ = lean_unbox(v_suppressElabErrors_157_);
v_res_161_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v___y_3443__boxed_159_, v_suppressElabErrors_boxed_160_, v_x_158_);
lean_dec(v_x_158_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(lean_object* v_ref_164_, lean_object* v_msgData_165_, uint8_t v_severity_166_, uint8_t v_isSilent_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v___y_172_; lean_object* v___y_173_; uint8_t v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___y_208_; uint8_t v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; uint8_t v___y_212_; uint8_t v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_233_; uint8_t v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; uint8_t v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_244_; uint8_t v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; uint8_t v___y_249_; uint8_t v___y_250_; uint8_t v___x_255_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; uint8_t v___y_262_; uint8_t v___y_263_; uint8_t v___y_265_; uint8_t v___x_280_; 
v___x_255_ = 2;
v___x_280_ = l_Lean_instBEqMessageSeverity_beq(v_severity_166_, v___x_255_);
if (v___x_280_ == 0)
{
v___y_265_ = v___x_280_;
goto v___jp_264_;
}
else
{
uint8_t v___x_281_; 
lean_inc_ref(v_msgData_165_);
v___x_281_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_165_);
v___y_265_ = v___x_281_;
goto v___jp_264_;
}
v___jp_171_:
{
lean_object* v___x_181_; lean_object* v_currNamespace_182_; lean_object* v_openDecls_183_; lean_object* v_env_184_; lean_object* v_nextMacroScope_185_; lean_object* v_ngen_186_; lean_object* v_auxDeclNGen_187_; lean_object* v_traceState_188_; lean_object* v_cache_189_; lean_object* v_messages_190_; lean_object* v_infoState_191_; lean_object* v_snapshotTasks_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_206_; 
v___x_181_ = lean_st_ref_take(v___y_180_);
v_currNamespace_182_ = lean_ctor_get(v___y_179_, 6);
v_openDecls_183_ = lean_ctor_get(v___y_179_, 7);
v_env_184_ = lean_ctor_get(v___x_181_, 0);
v_nextMacroScope_185_ = lean_ctor_get(v___x_181_, 1);
v_ngen_186_ = lean_ctor_get(v___x_181_, 2);
v_auxDeclNGen_187_ = lean_ctor_get(v___x_181_, 3);
v_traceState_188_ = lean_ctor_get(v___x_181_, 4);
v_cache_189_ = lean_ctor_get(v___x_181_, 5);
v_messages_190_ = lean_ctor_get(v___x_181_, 6);
v_infoState_191_ = lean_ctor_get(v___x_181_, 7);
v_snapshotTasks_192_ = lean_ctor_get(v___x_181_, 8);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_206_ == 0)
{
v___x_194_ = v___x_181_;
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_snapshotTasks_192_);
lean_inc(v_infoState_191_);
lean_inc(v_messages_190_);
lean_inc(v_cache_189_);
lean_inc(v_traceState_188_);
lean_inc(v_auxDeclNGen_187_);
lean_inc(v_ngen_186_);
lean_inc(v_nextMacroScope_185_);
lean_inc(v_env_184_);
lean_dec(v___x_181_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_openDecls_183_);
lean_inc(v_currNamespace_182_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_currNamespace_182_);
lean_ctor_set(v___x_196_, 1, v_openDecls_183_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___y_177_);
lean_inc_ref(v___y_173_);
lean_inc_ref(v___y_175_);
v___x_198_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_198_, 0, v___y_175_);
lean_ctor_set(v___x_198_, 1, v___y_178_);
lean_ctor_set(v___x_198_, 2, v___y_176_);
lean_ctor_set(v___x_198_, 3, v___y_173_);
lean_ctor_set(v___x_198_, 4, v___x_197_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*5, v___y_172_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*5 + 1, v___y_174_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*5 + 2, v_isSilent_167_);
v___x_199_ = l_Lean_MessageLog_add(v___x_198_, v_messages_190_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 6, v___x_199_);
v___x_201_ = v___x_194_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_env_184_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_nextMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_ngen_186_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_auxDeclNGen_187_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_traceState_188_);
lean_ctor_set(v_reuseFailAlloc_205_, 5, v_cache_189_);
lean_ctor_set(v_reuseFailAlloc_205_, 6, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 7, v_infoState_191_);
lean_ctor_set(v_reuseFailAlloc_205_, 8, v_snapshotTasks_192_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_st_ref_set(v___y_180_, v___x_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
v___jp_207_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_231_; 
v___x_216_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_165_);
v___x_217_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v___x_216_, v___y_168_, v___y_169_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_231_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref_n(v___y_210_, 2);
v___x_222_ = l_Lean_FileMap_toPosition(v___y_210_, v___y_214_);
lean_dec(v___y_214_);
v___x_223_ = l_Lean_FileMap_toPosition(v___y_210_, v___y_215_);
lean_dec(v___y_215_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___x_225_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0));
if (v___y_213_ == 0)
{
lean_del_object(v___x_220_);
lean_dec_ref(v___y_208_);
v___y_172_ = v___y_209_;
v___y_173_ = v___x_225_;
v___y_174_ = v___y_212_;
v___y_175_ = v___y_211_;
v___y_176_ = v___x_224_;
v___y_177_ = v_a_218_;
v___y_178_ = v___x_222_;
v___y_179_ = v___y_168_;
v___y_180_ = v___y_169_;
goto v___jp_171_;
}
else
{
uint8_t v___x_226_; 
lean_inc(v_a_218_);
v___x_226_ = l_Lean_MessageData_hasTag(v___y_208_, v_a_218_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec_ref(v___x_224_);
lean_dec_ref(v___x_222_);
lean_dec(v_a_218_);
v___x_227_ = lean_box(0);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_227_);
v___x_229_ = v___x_220_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
else
{
lean_del_object(v___x_220_);
v___y_172_ = v___y_209_;
v___y_173_ = v___x_225_;
v___y_174_ = v___y_212_;
v___y_175_ = v___y_211_;
v___y_176_ = v___x_224_;
v___y_177_ = v_a_218_;
v___y_178_ = v___x_222_;
v___y_179_ = v___y_168_;
v___y_180_ = v___y_169_;
goto v___jp_171_;
}
}
}
}
v___jp_232_:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Syntax_getTailPos_x3f(v___y_239_, v___y_234_);
lean_dec(v___y_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_inc(v___y_240_);
v___y_208_ = v___y_233_;
v___y_209_ = v___y_234_;
v___y_210_ = v___y_235_;
v___y_211_ = v___y_237_;
v___y_212_ = v___y_236_;
v___y_213_ = v___y_238_;
v___y_214_ = v___y_240_;
v___y_215_ = v___y_240_;
goto v___jp_207_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_242_);
lean_dec_ref(v___x_241_);
v___y_208_ = v___y_233_;
v___y_209_ = v___y_234_;
v___y_210_ = v___y_235_;
v___y_211_ = v___y_237_;
v___y_212_ = v___y_236_;
v___y_213_ = v___y_238_;
v___y_214_ = v___y_240_;
v___y_215_ = v_val_242_;
goto v___jp_207_;
}
}
v___jp_243_:
{
lean_object* v_ref_251_; lean_object* v___x_252_; 
v_ref_251_ = l_Lean_replaceRef(v_ref_164_, v___y_248_);
v___x_252_ = l_Lean_Syntax_getPos_x3f(v_ref_251_, v___y_245_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___y_233_ = v___y_244_;
v___y_234_ = v___y_245_;
v___y_235_ = v___y_246_;
v___y_236_ = v___y_250_;
v___y_237_ = v___y_247_;
v___y_238_ = v___y_249_;
v___y_239_ = v_ref_251_;
v___y_240_ = v___x_253_;
goto v___jp_232_;
}
else
{
lean_object* v_val_254_; 
v_val_254_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_254_);
lean_dec_ref(v___x_252_);
v___y_233_ = v___y_244_;
v___y_234_ = v___y_245_;
v___y_235_ = v___y_246_;
v___y_236_ = v___y_250_;
v___y_237_ = v___y_247_;
v___y_238_ = v___y_249_;
v___y_239_ = v_ref_251_;
v___y_240_ = v_val_254_;
goto v___jp_232_;
}
}
v___jp_256_:
{
if (v___y_263_ == 0)
{
v___y_244_ = v___y_261_;
v___y_245_ = v___y_262_;
v___y_246_ = v___y_257_;
v___y_247_ = v___y_258_;
v___y_248_ = v___y_259_;
v___y_249_ = v___y_260_;
v___y_250_ = v_severity_166_;
goto v___jp_243_;
}
else
{
v___y_244_ = v___y_261_;
v___y_245_ = v___y_262_;
v___y_246_ = v___y_257_;
v___y_247_ = v___y_258_;
v___y_248_ = v___y_259_;
v___y_249_ = v___y_260_;
v___y_250_ = v___x_255_;
goto v___jp_243_;
}
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
lean_object* v_fileName_266_; lean_object* v_fileMap_267_; lean_object* v_options_268_; lean_object* v_ref_269_; uint8_t v_suppressElabErrors_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___f_273_; uint8_t v___x_274_; uint8_t v___x_275_; 
v_fileName_266_ = lean_ctor_get(v___y_168_, 0);
v_fileMap_267_ = lean_ctor_get(v___y_168_, 1);
v_options_268_ = lean_ctor_get(v___y_168_, 2);
v_ref_269_ = lean_ctor_get(v___y_168_, 5);
v_suppressElabErrors_270_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*14 + 1);
v___x_271_ = lean_box(v___y_265_);
v___x_272_ = lean_box(v_suppressElabErrors_270_);
v___f_273_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_273_, 0, v___x_271_);
lean_closure_set(v___f_273_, 1, v___x_272_);
v___x_274_ = 1;
v___x_275_ = l_Lean_instBEqMessageSeverity_beq(v_severity_166_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_257_ = v_fileMap_267_;
v___y_258_ = v_fileName_266_;
v___y_259_ = v_ref_269_;
v___y_260_ = v_suppressElabErrors_270_;
v___y_261_ = v___f_273_;
v___y_262_ = v___y_265_;
v___y_263_ = v___x_275_;
goto v___jp_256_;
}
else
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = l_Lean_warningAsError;
v___x_277_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_options_268_, v___x_276_);
v___y_257_ = v_fileMap_267_;
v___y_258_ = v_fileName_266_;
v___y_259_ = v_ref_269_;
v___y_260_ = v_suppressElabErrors_270_;
v___y_261_ = v___f_273_;
v___y_262_ = v___y_265_;
v___y_263_ = v___x_277_;
goto v___jp_256_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_msgData_165_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_282_, lean_object* v_msgData_283_, lean_object* v_severity_284_, lean_object* v_isSilent_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
uint8_t v_severity_boxed_289_; uint8_t v_isSilent_boxed_290_; lean_object* v_res_291_; 
v_severity_boxed_289_ = lean_unbox(v_severity_284_);
v_isSilent_boxed_290_ = lean_unbox(v_isSilent_285_);
v_res_291_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_282_, v_msgData_283_, v_severity_boxed_289_, v_isSilent_boxed_290_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v_ref_282_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(lean_object* v_msgData_292_, uint8_t v_severity_293_, uint8_t v_isSilent_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_ref_298_; lean_object* v___x_299_; 
v_ref_298_ = lean_ctor_get(v___y_295_, 5);
v___x_299_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_298_, v_msgData_292_, v_severity_293_, v_isSilent_294_, v___y_295_, v___y_296_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(lean_object* v_msgData_300_, lean_object* v_severity_301_, lean_object* v_isSilent_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_severity_boxed_306_; uint8_t v_isSilent_boxed_307_; lean_object* v_res_308_; 
v_severity_boxed_306_ = lean_unbox(v_severity_301_);
v_isSilent_boxed_307_ = lean_unbox(v_isSilent_302_);
v_res_308_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_300_, v_severity_boxed_306_, v_isSilent_boxed_307_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = 1;
v___x_314_ = 0;
v___x_315_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(v_msgData_309_, v___x_313_, v___x_314_, v___y_310_, v___y_311_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v_msgData_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object* v_n_329_, uint8_t v_warning_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_options_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_options_338_ = lean_ctor_get(v_a_331_, 2);
v___x_339_ = l_Lean_exponentiation_threshold;
v___x_340_ = l_Lean_Option_get___at___00Lean_checkExponent_spec__0(v_options_338_, v___x_339_);
v___x_341_ = lean_nat_dec_lt(v___x_340_, v_n_329_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v___x_340_);
lean_dec(v_n_329_);
v___x_342_ = 1;
v___x_343_ = lean_box(v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
else
{
if (v_warning_330_ == 0)
{
lean_dec(v___x_340_);
lean_dec(v_n_329_);
goto v___jp_334_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_checkExponent___closed__1));
v___x_346_ = l_Lean_logMessageKind___redArg(v___x_345_, v_a_332_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_380_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_380_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_380_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_380_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
uint8_t v___x_351_; 
v___x_351_ = lean_unbox(v_a_347_);
if (v___x_351_ == 0)
{
lean_del_object(v___x_349_);
lean_dec(v_a_347_);
lean_dec(v___x_340_);
lean_dec(v_n_329_);
goto v___jp_334_;
}
else
{
lean_object* v_name_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v_name_352_ = lean_ctor_get(v___x_339_, 0);
v___x_353_ = ((lean_object*)(l_Lean_checkExponent___closed__2));
v___x_354_ = l_Nat_reprFast(v_n_329_);
v___x_355_ = lean_string_append(v___x_353_, v___x_354_);
lean_dec_ref(v___x_354_);
v___x_356_ = ((lean_object*)(l_Lean_checkExponent___closed__3));
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
v___x_358_ = l_Nat_reprFast(v___x_340_);
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = ((lean_object*)(l_Lean_checkExponent___closed__4));
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = lean_unbox(v_a_347_);
lean_dec(v_a_347_);
lean_inc(v_name_352_);
v___x_363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_352_, v___x_362_);
v___x_364_ = lean_string_append(v___x_361_, v___x_363_);
lean_dec_ref(v___x_363_);
v___x_365_ = ((lean_object*)(l_Lean_checkExponent___closed__5));
v___x_366_ = lean_string_append(v___x_364_, v___x_365_);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 3);
lean_ctor_set(v___x_349_, 0, v___x_366_);
v___x_368_ = v___x_349_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_379_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_MessageData_ofFormat(v___x_368_);
v___x_370_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(v___x_369_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec_ref(v___x_370_);
goto v___jp_334_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_340_);
lean_dec(v_n_329_);
return v___x_346_;
}
}
}
v___jp_334_:
{
uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = 0;
v___x_336_ = lean_box(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object* v_n_381_, lean_object* v_warning_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
uint8_t v_warning_boxed_386_; lean_object* v_res_387_; 
v_warning_boxed_386_ = lean_unbox(v_warning_382_);
v_res_387_ = l_Lean_checkExponent(v_n_381_, v_warning_boxed_386_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_387_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
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
