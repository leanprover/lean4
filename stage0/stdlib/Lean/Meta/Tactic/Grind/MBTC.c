// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MBTC
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Canon import Lean.Meta.Tactic.Grind.CastLike
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value;
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "__grind_main_arg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 28, 25, 170, 231, 254, 59, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "__grind_other_arg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 27, 42, 236, 138, 38, 28, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_lt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_SplitInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__1_value),LEAN_SCALAR_PTR_LITERAL(241, 58, 101, 243, 41, 236, 253, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isKnownCaseSplit___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_SplitInfo_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 200, 238, 83, 121, 101, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__2_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__4_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_mbtc___closed__0;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__1;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mbtc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__2_value;
lean_object* l_Lean_Meta_Grind_SplitInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_SplitInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__3_value;
lean_object* l_Lean_Meta_Grind_SplitInfo_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mbtc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_SplitInfo_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__4_value;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mbtc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__5_value;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__6;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "skipping `mbtc`, maximum number of splits has been reached `(splits := "};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__7_value;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__8;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__9_value;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__10;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Expr_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_4, x_1);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_2, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_array_fget_borrowed(x_5, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_21);
x_22 = l_Lean_Meta_Grind_Canon_isSupport(x_20, x_4, x_21, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_27 = lean_unbox(x_23);
lean_dec(x_23);
if (x_27 == 0)
{
goto block_26;
}
else
{
if (x_19 == 0)
{
x_11 = x_5;
x_12 = lean_box(0);
goto block_16;
}
else
{
goto block_26;
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
x_25 = lean_array_fset(x_5, x_4, x_24);
x_11 = x_25;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
x_32 = lean_array_fset(x_5, x_4, x_31);
x_11 = x_32;
x_12 = lean_box(0);
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_array_set(x_3, x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_2 = x_10;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_getFunInfo(x_2, x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_array_get_size(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(x_19, x_1, x_18, x_20, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_mkAppN(x_2, x_23);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_mkAppN(x_2, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_2);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
x_9 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_9);
x_10 = lean_mk_array(x_9, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_9, x_11);
lean_dec(x_9);
x_13 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(x_2, x_1, x_10, x_12, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(x_1, x_2, x_3, x_7, x_8, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_44; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
x_44 = lean_expr_lt(x_15, x_17);
if (x_44 == 0)
{
x_19 = x_17;
x_20 = x_15;
goto block_43;
}
else
{
x_19 = x_15;
x_20 = x_17;
goto block_43;
}
block_43:
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_21 = l_Lean_Meta_mkEq(x_19, x_20, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_9);
x_23 = lean_grind_canon(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Sym_shareCommon___redArg(x_24, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_3);
lean_inc_ref(x_18);
lean_inc_ref(x_16);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_3);
x_29 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
lean_inc(x_3);
lean_inc_ref(x_18);
lean_inc_ref(x_16);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_3);
x_32 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_9);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Meta_isInstance___redArg(x_4, x_2);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_2, x_4);
x_20 = l_Lean_Meta_Grind_addSplitCandidate(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
size_t x_21; size_t x_22; 
lean_dec_ref(x_20);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
{
size_t _tmp_3 = x_22;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(x_4, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_eq(x_2, x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget(x_1, x_2);
x_24 = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(x_23, x_5);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_72; lean_object* x_73; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_29);
x_72 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___closed__2));
x_73 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_72, x_13);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = x_14;
x_59 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_inc_ref(x_29);
x_76 = l_Lean_MessageData_ofExpr(x_29);
x_77 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_72, x_76, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = x_14;
x_59 = lean_box(0);
goto block_71;
}
else
{
uint8_t x_78; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
block_48:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = lean_grind_internalize(x_29, x_41, x_42, x_32, x_37, x_33, x_40, x_36, x_34, x_38, x_30, x_39, x_35);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec_ref(x_43);
x_44 = lean_array_push(x_4, x_23);
x_16 = x_44;
x_17 = lean_box(0);
goto block_21;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
block_71:
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_getGeneration___redArg(x_27, x_49);
lean_dec_ref(x_27);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = l_Lean_Meta_Grind_getGeneration___redArg(x_28, x_49);
lean_dec_ref(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_nat_dec_le(x_61, x_63);
if (x_64 == 0)
{
lean_dec(x_63);
x_30 = x_56;
x_31 = lean_box(0);
x_32 = x_49;
x_33 = x_51;
x_34 = x_54;
x_35 = x_58;
x_36 = x_53;
x_37 = x_50;
x_38 = x_55;
x_39 = x_57;
x_40 = x_52;
x_41 = x_61;
goto block_48;
}
else
{
lean_dec(x_61);
x_30 = x_56;
x_31 = lean_box(0);
x_32 = x_49;
x_33 = x_51;
x_34 = x_54;
x_35 = x_58;
x_36 = x_53;
x_37 = x_50;
x_38 = x_55;
x_39 = x_57;
x_40 = x_52;
x_41 = x_63;
goto block_48;
}
}
else
{
uint8_t x_65; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_29);
lean_dec_ref(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_dec(x_23);
x_16 = x_4;
x_17 = lean_box(0);
goto block_21;
}
}
else
{
lean_dec(x_23);
x_16 = x_4;
x_17 = lean_box(0);
goto block_21;
}
}
else
{
uint8_t x_84; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_84 = !lean_is_exclusive(x_24);
if (x_84 == 0)
{
return x_24;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_24, 0);
lean_inc(x_85);
lean_dec(x_24);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_4);
return x_87;
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_1);
return x_18;
}
}
static lean_object* _init_l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0;
x_16 = lean_nat_dec_lt(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_le(x_3, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_2, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_2);
x_23 = lean_usize_of_nat(x_18);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18(x_1, x_22, x_23, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_24;
}
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_2);
x_26 = lean_usize_of_nat(x_3);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__18(x_1, x_25, x_26, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Meta_Grind_SplitInfo_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Meta_Grind_SplitInfo_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Meta_Grind_SplitInfo_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Meta_Grind_SplitInfo_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec_ref(x_5);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_22);
lean_inc_ref(x_2);
x_23 = lean_apply_13(x_21, x_2, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_dec(x_19);
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_27; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_22);
lean_inc_ref(x_2);
x_27 = l_Lean_Meta_Grind_hasSameType(x_2, x_22, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_dec(x_19);
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_31; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
x_31 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(x_3, x_19, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_box(0);
x_34 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(x_6, x_32, x_33);
x_5 = x_20;
x_6 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_36; 
x_36 = lean_usize_dec_lt(x_8, x_7);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_9);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_st_ref_get(x_10);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_array_uget(x_6, x_8);
x_46 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_38, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 1)
{
uint8_t x_47; 
lean_free_object(x_40);
lean_free_object(x_9);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_49);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_48);
x_50 = lean_apply_12(x_49, x_48, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_free_object(x_46);
lean_dec(x_48);
x_27 = x_42;
x_28 = x_43;
x_29 = x_44;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_54 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_53, x_18);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_90; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_48);
x_56 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_56, 0, x_48);
x_90 = lean_unbox(x_55);
lean_dec(x_55);
if (x_90 == 0)
{
lean_free_object(x_46);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = x_42;
x_58 = x_44;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
x_68 = x_19;
x_69 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_48);
x_91 = l_Lean_MessageData_ofExpr(x_48);
x_92 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_inc_ref(x_5);
x_94 = l_Lean_MessageData_ofExpr(x_5);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_43);
x_98 = l_Nat_reprFast(x_43);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_98);
x_99 = l_Lean_MessageData_ofFormat(x_46);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_53, x_100, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_101) == 0)
{
lean_dec_ref(x_101);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = x_42;
x_58 = x_44;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
x_68 = x_19;
x_69 = lean_box(0);
goto block_89;
}
else
{
uint8_t x_102; 
lean_dec_ref(x_56);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
block_89:
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_1);
lean_inc(x_48);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_48);
lean_ctor_set(x_70, 1, x_1);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc_ref(x_1);
x_71 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_43, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_58, x_72);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
lean_inc(x_74);
x_75 = l_List_any___redArg(x_74, x_56);
if (x_75 == 0)
{
lean_object* x_76; 
lean_inc(x_74);
lean_inc(x_43);
lean_inc_ref(x_70);
lean_inc_ref(x_2);
x_76 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_48, x_70, x_43, x_74, x_57, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_74);
x_79 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_58, x_72, x_78);
x_27 = x_77;
x_28 = x_43;
x_29 = x_79;
x_30 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_80; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_58);
lean_dec(x_43);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
x_27 = x_57;
x_28 = x_43;
x_29 = x_58;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_73);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_56);
lean_dec(x_48);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_70);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_58, x_72, x_84);
x_27 = x_57;
x_28 = x_43;
x_29 = x_85;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
uint8_t x_86; 
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_71);
if (x_86 == 0)
{
return x_71;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
lean_dec(x_71);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_54);
if (x_105 == 0)
{
return x_54;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_54, 0);
lean_inc(x_106);
lean_dec(x_54);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_108 = !lean_is_exclusive(x_50);
if (x_108 == 0)
{
return x_50;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_50, 0);
lean_inc(x_109);
lean_dec(x_50);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_46, 0);
lean_inc(x_111);
lean_dec(x_46);
x_112 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_112);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_111);
x_113 = lean_apply_12(x_112, x_111, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_dec(x_111);
x_27 = x_42;
x_28 = x_43;
x_29 = x_44;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_117 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_116, x_18);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_153; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_inc(x_111);
x_119 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_119, 0, x_111);
x_153 = lean_unbox(x_118);
lean_dec(x_118);
if (x_153 == 0)
{
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_120 = x_42;
x_121 = x_44;
x_122 = x_10;
x_123 = x_11;
x_124 = x_12;
x_125 = x_13;
x_126 = x_14;
x_127 = x_15;
x_128 = x_16;
x_129 = x_17;
x_130 = x_18;
x_131 = x_19;
x_132 = lean_box(0);
goto block_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_inc(x_111);
x_154 = l_Lean_MessageData_ofExpr(x_111);
x_155 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
lean_inc_ref(x_5);
x_157 = l_Lean_MessageData_ofExpr(x_5);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_43);
x_161 = l_Nat_reprFast(x_43);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = l_Lean_MessageData_ofFormat(x_162);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_116, x_164, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_165) == 0)
{
lean_dec_ref(x_165);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_120 = x_42;
x_121 = x_44;
x_122 = x_10;
x_123 = x_11;
x_124 = x_12;
x_125 = x_13;
x_126 = x_14;
x_127 = x_15;
x_128 = x_16;
x_129 = x_17;
x_130 = x_18;
x_131 = x_19;
x_132 = lean_box(0);
goto block_152;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_119);
lean_dec(x_111);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
block_152:
{
lean_object* x_133; lean_object* x_134; 
lean_inc_ref(x_1);
lean_inc(x_111);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_111);
lean_ctor_set(x_133, 1, x_1);
lean_inc(x_131);
lean_inc_ref(x_130);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc_ref(x_1);
x_134 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_43, x_128, x_129, x_130, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_121, x_135);
if (lean_obj_tag(x_136) == 1)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
lean_inc(x_137);
x_138 = l_List_any___redArg(x_137, x_119);
if (x_138 == 0)
{
lean_object* x_139; 
lean_inc(x_137);
lean_inc(x_43);
lean_inc_ref(x_133);
lean_inc_ref(x_2);
x_139 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_111, x_133, x_43, x_137, x_120, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129, x_130, x_131);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_133);
lean_ctor_set(x_141, 1, x_137);
x_142 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_121, x_135, x_141);
x_27 = x_140;
x_28 = x_43;
x_29 = x_142;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_137);
lean_dec(x_135);
lean_dec_ref(x_133);
lean_dec_ref(x_121);
lean_dec(x_43);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_139, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_dec(x_137);
lean_dec(x_135);
lean_dec_ref(x_133);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_111);
x_27 = x_120;
x_28 = x_43;
x_29 = x_121;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_136);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec_ref(x_119);
lean_dec(x_111);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_121, x_135, x_147);
x_27 = x_120;
x_28 = x_43;
x_29 = x_148;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_133);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec(x_111);
lean_dec(x_43);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_111);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_169 = lean_ctor_get(x_117, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_170 = x_117;
} else {
 lean_dec_ref(x_117);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_111);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_172 = lean_ctor_get(x_113, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_173 = x_113;
} else {
 lean_dec_ref(x_113);
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
}
else
{
lean_dec(x_46);
x_21 = x_9;
x_22 = lean_box(0);
goto block_26;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_9, 0);
x_176 = lean_ctor_get(x_40, 0);
x_177 = lean_ctor_get(x_40, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_40);
x_178 = lean_array_uget(x_6, x_8);
x_179 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_38, x_178);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 1)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_free_object(x_9);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_182);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_180);
x_183 = lean_apply_12(x_182, x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
x_27 = x_175;
x_28 = x_176;
x_29 = x_177;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_187 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_186, x_18);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_223; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
lean_inc(x_180);
x_189 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_189, 0, x_180);
x_223 = lean_unbox(x_188);
lean_dec(x_188);
if (x_223 == 0)
{
lean_dec(x_181);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_190 = x_175;
x_191 = x_177;
x_192 = x_10;
x_193 = x_11;
x_194 = x_12;
x_195 = x_13;
x_196 = x_14;
x_197 = x_15;
x_198 = x_16;
x_199 = x_17;
x_200 = x_18;
x_201 = x_19;
x_202 = lean_box(0);
goto block_222;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_inc(x_180);
x_224 = l_Lean_MessageData_ofExpr(x_180);
x_225 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_inc_ref(x_5);
x_227 = l_Lean_MessageData_ofExpr(x_5);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
lean_inc(x_176);
x_231 = l_Nat_reprFast(x_176);
if (lean_is_scalar(x_181)) {
 x_232 = lean_alloc_ctor(3, 1, 0);
} else {
 x_232 = x_181;
 lean_ctor_set_tag(x_232, 3);
}
lean_ctor_set(x_232, 0, x_231);
x_233 = l_Lean_MessageData_ofFormat(x_232);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_186, x_234, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_235) == 0)
{
lean_dec_ref(x_235);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_190 = x_175;
x_191 = x_177;
x_192 = x_10;
x_193 = x_11;
x_194 = x_12;
x_195 = x_13;
x_196 = x_14;
x_197 = x_15;
x_198 = x_16;
x_199 = x_17;
x_200 = x_18;
x_201 = x_19;
x_202 = lean_box(0);
goto block_222;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec_ref(x_189);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
}
block_222:
{
lean_object* x_203; lean_object* x_204; 
lean_inc_ref(x_1);
lean_inc(x_180);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_180);
lean_ctor_set(x_203, 1, x_1);
lean_inc(x_201);
lean_inc_ref(x_200);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc_ref(x_1);
x_204 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_176, x_198, x_199, x_200, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_191, x_205);
if (lean_obj_tag(x_206) == 1)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec_ref(x_206);
lean_inc(x_207);
x_208 = l_List_any___redArg(x_207, x_189);
if (x_208 == 0)
{
lean_object* x_209; 
lean_inc(x_207);
lean_inc(x_176);
lean_inc_ref(x_203);
lean_inc_ref(x_2);
x_209 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_180, x_203, x_176, x_207, x_190, x_192, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_203);
lean_ctor_set(x_211, 1, x_207);
x_212 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_191, x_205, x_211);
x_27 = x_210;
x_28 = x_176;
x_29 = x_212;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_207);
lean_dec(x_205);
lean_dec_ref(x_203);
lean_dec_ref(x_191);
lean_dec(x_176);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_214 = x_209;
} else {
 lean_dec_ref(x_209);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
}
else
{
lean_dec(x_207);
lean_dec(x_205);
lean_dec_ref(x_203);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_180);
x_27 = x_190;
x_28 = x_176;
x_29 = x_191;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_189);
lean_dec(x_180);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_203);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_191, x_205, x_217);
x_27 = x_190;
x_28 = x_176;
x_29 = x_218;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_203);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_189);
lean_dec(x_180);
lean_dec(x_176);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_219 = lean_ctor_get(x_204, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_220 = x_204;
} else {
 lean_dec_ref(x_204);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_187, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_240 = x_187;
} else {
 lean_dec_ref(x_187);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_242 = lean_ctor_get(x_183, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_243 = x_183;
} else {
 lean_dec_ref(x_183);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
}
else
{
lean_object* x_245; 
lean_dec(x_179);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_176);
lean_ctor_set(x_245, 1, x_177);
lean_ctor_set(x_9, 1, x_245);
x_21 = x_9;
x_22 = lean_box(0);
goto block_26;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_9, 1);
x_247 = lean_ctor_get(x_9, 0);
lean_inc(x_246);
lean_inc(x_247);
lean_dec(x_9);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_250 = x_246;
} else {
 lean_dec_ref(x_246);
 x_250 = lean_box(0);
}
x_251 = lean_array_uget(x_6, x_8);
x_252 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_38, x_251);
lean_dec(x_251);
if (lean_obj_tag(x_252) == 1)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_250);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_255);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_253);
x_256 = lean_apply_12(x_255, x_253, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_dec(x_254);
lean_dec(x_253);
x_27 = x_247;
x_28 = x_248;
x_29 = x_249;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_260 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_259, x_18);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_296; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec_ref(x_260);
lean_inc(x_253);
x_262 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_262, 0, x_253);
x_296 = lean_unbox(x_261);
lean_dec(x_261);
if (x_296 == 0)
{
lean_dec(x_254);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_263 = x_247;
x_264 = x_249;
x_265 = x_10;
x_266 = x_11;
x_267 = x_12;
x_268 = x_13;
x_269 = x_14;
x_270 = x_15;
x_271 = x_16;
x_272 = x_17;
x_273 = x_18;
x_274 = x_19;
x_275 = lean_box(0);
goto block_295;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_inc(x_253);
x_297 = l_Lean_MessageData_ofExpr(x_253);
x_298 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
lean_inc_ref(x_5);
x_300 = l_Lean_MessageData_ofExpr(x_5);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
lean_inc(x_248);
x_304 = l_Nat_reprFast(x_248);
if (lean_is_scalar(x_254)) {
 x_305 = lean_alloc_ctor(3, 1, 0);
} else {
 x_305 = x_254;
 lean_ctor_set_tag(x_305, 3);
}
lean_ctor_set(x_305, 0, x_304);
x_306 = l_Lean_MessageData_ofFormat(x_305);
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_259, x_307, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_308);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_263 = x_247;
x_264 = x_249;
x_265 = x_10;
x_266 = x_11;
x_267 = x_12;
x_268 = x_13;
x_269 = x_14;
x_270 = x_15;
x_271 = x_16;
x_272 = x_17;
x_273 = x_18;
x_274 = x_19;
x_275 = lean_box(0);
goto block_295;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec_ref(x_262);
lean_dec(x_253);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_310 = x_308;
} else {
 lean_dec_ref(x_308);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_309);
return x_311;
}
}
block_295:
{
lean_object* x_276; lean_object* x_277; 
lean_inc_ref(x_1);
lean_inc(x_253);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_253);
lean_ctor_set(x_276, 1, x_1);
lean_inc(x_274);
lean_inc_ref(x_273);
lean_inc(x_272);
lean_inc_ref(x_271);
lean_inc_ref(x_1);
x_277 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_248, x_271, x_272, x_273, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec_ref(x_277);
x_279 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_264, x_278);
if (lean_obj_tag(x_279) == 1)
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec_ref(x_279);
lean_inc(x_280);
x_281 = l_List_any___redArg(x_280, x_262);
if (x_281 == 0)
{
lean_object* x_282; 
lean_inc(x_280);
lean_inc(x_248);
lean_inc_ref(x_276);
lean_inc_ref(x_2);
x_282 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_253, x_276, x_248, x_280, x_263, x_265, x_266, x_267, x_268, x_269, x_270, x_271, x_272, x_273, x_274);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_276);
lean_ctor_set(x_284, 1, x_280);
x_285 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_264, x_278, x_284);
x_27 = x_283;
x_28 = x_248;
x_29 = x_285;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_280);
lean_dec(x_278);
lean_dec_ref(x_276);
lean_dec_ref(x_264);
lean_dec(x_248);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_287 = x_282;
} else {
 lean_dec_ref(x_282);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
}
else
{
lean_dec(x_280);
lean_dec(x_278);
lean_dec_ref(x_276);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_253);
x_27 = x_263;
x_28 = x_248;
x_29 = x_264;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_279);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec_ref(x_262);
lean_dec(x_253);
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_276);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_264, x_278, x_290);
x_27 = x_263;
x_28 = x_248;
x_29 = x_291;
x_30 = lean_box(0);
goto block_35;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec_ref(x_276);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec(x_253);
lean_dec(x_248);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_292 = lean_ctor_get(x_277, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_293 = x_277;
} else {
 lean_dec_ref(x_277);
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
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_312 = lean_ctor_get(x_260, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_313 = x_260;
} else {
 lean_dec_ref(x_260);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_315 = lean_ctor_get(x_256, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_316 = x_256;
} else {
 lean_dec_ref(x_256);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_252);
if (lean_is_scalar(x_250)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_250;
}
lean_ctor_set(x_318, 0, x_248);
lean_ctor_set(x_318, 1, x_249);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_247);
lean_ctor_set(x_319, 1, x_318);
x_21 = x_319;
x_22 = lean_box(0);
goto block_26;
}
}
}
block_26:
{
size_t x_23; size_t x_24; 
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_21;
goto _start;
}
block_35:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_28, x_31);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_21 = x_34;
x_22 = lean_box(0);
goto block_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___boxed(lean_object** _args) {
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
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_38; 
x_38 = lean_usize_dec_lt(x_10, x_9);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_11);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_st_ref_get(x_12);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_11, 1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_array_uget(x_8, x_10);
x_48 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_40, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 1)
{
uint8_t x_49; 
lean_free_object(x_42);
lean_free_object(x_11);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_51);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_50);
x_52 = lean_apply_12(x_51, x_50, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0));
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_free_object(x_48);
lean_dec(x_50);
x_29 = x_44;
x_30 = x_45;
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_56 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_55, x_20);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_92; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_50);
x_58 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_58, 0, x_50);
x_92 = lean_unbox(x_57);
lean_dec(x_57);
if (x_92 == 0)
{
lean_free_object(x_48);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_59 = x_44;
x_60 = x_46;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
x_68 = x_19;
x_69 = x_20;
x_70 = x_21;
x_71 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_inc(x_50);
x_93 = l_Lean_MessageData_ofExpr(x_50);
x_94 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc_ref(x_7);
x_96 = l_Lean_MessageData_ofExpr(x_7);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_45);
x_100 = l_Nat_reprFast(x_45);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 0, x_100);
x_101 = l_Lean_MessageData_ofFormat(x_48);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_55, x_102, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_103) == 0)
{
lean_dec_ref(x_103);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_59 = x_44;
x_60 = x_46;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
x_68 = x_19;
x_69 = x_20;
x_70 = x_21;
x_71 = lean_box(0);
goto block_91;
}
else
{
uint8_t x_104; 
lean_dec_ref(x_58);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
block_91:
{
lean_object* x_72; lean_object* x_73; 
lean_inc_ref(x_1);
lean_inc(x_50);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_50);
lean_ctor_set(x_72, 1, x_1);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc_ref(x_1);
x_73 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_45, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_60, x_74);
if (lean_obj_tag(x_75) == 1)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc(x_76);
x_77 = l_List_any___redArg(x_76, x_58);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc(x_76);
lean_inc(x_45);
lean_inc_ref(x_72);
lean_inc_ref(x_2);
x_78 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_50, x_72, x_45, x_76, x_59, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_76);
x_81 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_60, x_74, x_80);
x_29 = x_79;
x_30 = x_45;
x_31 = x_81;
x_32 = lean_box(0);
goto block_37;
}
else
{
uint8_t x_82; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_60);
lean_dec(x_45);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
return x_78;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
lean_dec(x_76);
lean_dec(x_74);
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_50);
x_29 = x_59;
x_30 = x_45;
x_31 = x_60;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_75);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_58);
lean_dec(x_50);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_60, x_74, x_86);
x_29 = x_59;
x_30 = x_45;
x_31 = x_87;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_73);
if (x_88 == 0)
{
return x_73;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
lean_dec(x_73);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_107; 
lean_free_object(x_48);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_56);
if (x_107 == 0)
{
return x_56;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_56, 0);
lean_inc(x_108);
lean_dec(x_56);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_48);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_52);
if (x_110 == 0)
{
return x_52;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_52, 0);
lean_inc(x_111);
lean_dec(x_52);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_48, 0);
lean_inc(x_113);
lean_dec(x_48);
x_114 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_114);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_113);
x_115 = lean_apply_12(x_114, x_113, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0));
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_dec(x_113);
x_29 = x_44;
x_30 = x_45;
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_119 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_118, x_20);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_155; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
lean_inc(x_113);
x_121 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_121, 0, x_113);
x_155 = lean_unbox(x_120);
lean_dec(x_120);
if (x_155 == 0)
{
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_122 = x_44;
x_123 = x_46;
x_124 = x_12;
x_125 = x_13;
x_126 = x_14;
x_127 = x_15;
x_128 = x_16;
x_129 = x_17;
x_130 = x_18;
x_131 = x_19;
x_132 = x_20;
x_133 = x_21;
x_134 = lean_box(0);
goto block_154;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_inc(x_113);
x_156 = l_Lean_MessageData_ofExpr(x_113);
x_157 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_inc_ref(x_7);
x_159 = l_Lean_MessageData_ofExpr(x_7);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_45);
x_163 = l_Nat_reprFast(x_45);
x_164 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_MessageData_ofFormat(x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_118, x_166, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_167);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_122 = x_44;
x_123 = x_46;
x_124 = x_12;
x_125 = x_13;
x_126 = x_14;
x_127 = x_15;
x_128 = x_16;
x_129 = x_17;
x_130 = x_18;
x_131 = x_19;
x_132 = x_20;
x_133 = x_21;
x_134 = lean_box(0);
goto block_154;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_121);
lean_dec(x_113);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
}
block_154:
{
lean_object* x_135; lean_object* x_136; 
lean_inc_ref(x_1);
lean_inc(x_113);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_1);
lean_inc(x_133);
lean_inc_ref(x_132);
lean_inc(x_131);
lean_inc_ref(x_130);
lean_inc_ref(x_1);
x_136 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_45, x_130, x_131, x_132, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_123, x_137);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
lean_inc(x_139);
x_140 = l_List_any___redArg(x_139, x_121);
if (x_140 == 0)
{
lean_object* x_141; 
lean_inc(x_139);
lean_inc(x_45);
lean_inc_ref(x_135);
lean_inc_ref(x_2);
x_141 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_113, x_135, x_45, x_139, x_122, x_124, x_125, x_126, x_127, x_128, x_129, x_130, x_131, x_132, x_133);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_139);
x_144 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_123, x_137, x_143);
x_29 = x_142;
x_30 = x_45;
x_31 = x_144;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec_ref(x_135);
lean_dec_ref(x_123);
lean_dec(x_45);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
else
{
lean_dec(x_139);
lean_dec(x_137);
lean_dec_ref(x_135);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_113);
x_29 = x_122;
x_30 = x_45;
x_31 = x_123;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec_ref(x_121);
lean_dec(x_113);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_123, x_137, x_149);
x_29 = x_122;
x_30 = x_45;
x_31 = x_150;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_135);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_113);
lean_dec(x_45);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_136, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_152 = x_136;
} else {
 lean_dec_ref(x_136);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_113);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_171 = lean_ctor_get(x_119, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_172 = x_119;
} else {
 lean_dec_ref(x_119);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_113);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_115, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_175 = x_115;
} else {
 lean_dec_ref(x_115);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
}
else
{
lean_dec(x_48);
x_23 = x_11;
x_24 = lean_box(0);
goto block_28;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_11, 0);
x_178 = lean_ctor_get(x_42, 0);
x_179 = lean_ctor_get(x_42, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_42);
x_180 = lean_array_uget(x_8, x_10);
x_181 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_40, x_180);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 1)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_free_object(x_11);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_184);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_182);
x_185 = lean_apply_12(x_184, x_182, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0));
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_dec(x_183);
lean_dec(x_182);
x_29 = x_177;
x_30 = x_178;
x_31 = x_179;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_189 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_188, x_20);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_225; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
lean_inc(x_182);
x_191 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_191, 0, x_182);
x_225 = lean_unbox(x_190);
lean_dec(x_190);
if (x_225 == 0)
{
lean_dec(x_183);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_192 = x_177;
x_193 = x_179;
x_194 = x_12;
x_195 = x_13;
x_196 = x_14;
x_197 = x_15;
x_198 = x_16;
x_199 = x_17;
x_200 = x_18;
x_201 = x_19;
x_202 = x_20;
x_203 = x_21;
x_204 = lean_box(0);
goto block_224;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_inc(x_182);
x_226 = l_Lean_MessageData_ofExpr(x_182);
x_227 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
lean_inc_ref(x_7);
x_229 = l_Lean_MessageData_ofExpr(x_7);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
lean_inc(x_178);
x_233 = l_Nat_reprFast(x_178);
if (lean_is_scalar(x_183)) {
 x_234 = lean_alloc_ctor(3, 1, 0);
} else {
 x_234 = x_183;
 lean_ctor_set_tag(x_234, 3);
}
lean_ctor_set(x_234, 0, x_233);
x_235 = l_Lean_MessageData_ofFormat(x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_188, x_236, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_237) == 0)
{
lean_dec_ref(x_237);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_192 = x_177;
x_193 = x_179;
x_194 = x_12;
x_195 = x_13;
x_196 = x_14;
x_197 = x_15;
x_198 = x_16;
x_199 = x_17;
x_200 = x_18;
x_201 = x_19;
x_202 = x_20;
x_203 = x_21;
x_204 = lean_box(0);
goto block_224;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_191);
lean_dec(x_182);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
block_224:
{
lean_object* x_205; lean_object* x_206; 
lean_inc_ref(x_1);
lean_inc(x_182);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_182);
lean_ctor_set(x_205, 1, x_1);
lean_inc(x_203);
lean_inc_ref(x_202);
lean_inc(x_201);
lean_inc_ref(x_200);
lean_inc_ref(x_1);
x_206 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_178, x_200, x_201, x_202, x_203);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec_ref(x_206);
x_208 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_193, x_207);
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
lean_inc(x_209);
x_210 = l_List_any___redArg(x_209, x_191);
if (x_210 == 0)
{
lean_object* x_211; 
lean_inc(x_209);
lean_inc(x_178);
lean_inc_ref(x_205);
lean_inc_ref(x_2);
x_211 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_182, x_205, x_178, x_209, x_192, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_205);
lean_ctor_set(x_213, 1, x_209);
x_214 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_193, x_207, x_213);
x_29 = x_212;
x_30 = x_178;
x_31 = x_214;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_209);
lean_dec(x_207);
lean_dec_ref(x_205);
lean_dec_ref(x_193);
lean_dec(x_178);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_215 = lean_ctor_get(x_211, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_dec(x_209);
lean_dec(x_207);
lean_dec_ref(x_205);
lean_dec(x_203);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_182);
x_29 = x_192;
x_30 = x_178;
x_31 = x_193;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_208);
lean_dec(x_203);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_191);
lean_dec(x_182);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_205);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_193, x_207, x_219);
x_29 = x_192;
x_30 = x_178;
x_31 = x_220;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_205);
lean_dec(x_203);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_221 = lean_ctor_get(x_206, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_222 = x_206;
} else {
 lean_dec_ref(x_206);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_221);
return x_223;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_241 = lean_ctor_get(x_189, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_242 = x_189;
} else {
 lean_dec_ref(x_189);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_244 = lean_ctor_get(x_185, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_245 = x_185;
} else {
 lean_dec_ref(x_185);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
}
else
{
lean_object* x_247; 
lean_dec(x_181);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_178);
lean_ctor_set(x_247, 1, x_179);
lean_ctor_set(x_11, 1, x_247);
x_23 = x_11;
x_24 = lean_box(0);
goto block_28;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_248 = lean_ctor_get(x_11, 1);
x_249 = lean_ctor_get(x_11, 0);
lean_inc(x_248);
lean_inc(x_249);
lean_dec(x_11);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_253 = lean_array_uget(x_8, x_10);
x_254 = l_Lean_Meta_Grind_Goal_getRoot_x3f(x_40, x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 1)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_257);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_255);
x_258 = lean_apply_12(x_257, x_255, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0));
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = lean_unbox(x_259);
lean_dec(x_259);
if (x_260 == 0)
{
lean_dec(x_256);
lean_dec(x_255);
x_29 = x_249;
x_30 = x_250;
x_31 = x_251;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__1));
x_262 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(x_261, x_20);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_298; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
lean_inc(x_255);
x_264 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_264, 0, x_255);
x_298 = lean_unbox(x_263);
lean_dec(x_263);
if (x_298 == 0)
{
lean_dec(x_256);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_265 = x_249;
x_266 = x_251;
x_267 = x_12;
x_268 = x_13;
x_269 = x_14;
x_270 = x_15;
x_271 = x_16;
x_272 = x_17;
x_273 = x_18;
x_274 = x_19;
x_275 = x_20;
x_276 = x_21;
x_277 = lean_box(0);
goto block_297;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_inc(x_255);
x_299 = l_Lean_MessageData_ofExpr(x_255);
x_300 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3;
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
lean_inc_ref(x_7);
x_302 = l_Lean_MessageData_ofExpr(x_7);
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5;
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
lean_inc(x_250);
x_306 = l_Nat_reprFast(x_250);
if (lean_is_scalar(x_256)) {
 x_307 = lean_alloc_ctor(3, 1, 0);
} else {
 x_307 = x_256;
 lean_ctor_set_tag(x_307, 3);
}
lean_ctor_set(x_307, 0, x_306);
x_308 = l_Lean_MessageData_ofFormat(x_307);
x_309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_309, 0, x_305);
lean_ctor_set(x_309, 1, x_308);
x_310 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_261, x_309, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_310) == 0)
{
lean_dec_ref(x_310);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_265 = x_249;
x_266 = x_251;
x_267 = x_12;
x_268 = x_13;
x_269 = x_14;
x_270 = x_15;
x_271 = x_16;
x_272 = x_17;
x_273 = x_18;
x_274 = x_19;
x_275 = x_20;
x_276 = x_21;
x_277 = lean_box(0);
goto block_297;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec_ref(x_264);
lean_dec(x_255);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
}
block_297:
{
lean_object* x_278; lean_object* x_279; 
lean_inc_ref(x_1);
lean_inc(x_255);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_255);
lean_ctor_set(x_278, 1, x_1);
lean_inc(x_276);
lean_inc_ref(x_275);
lean_inc(x_274);
lean_inc_ref(x_273);
lean_inc_ref(x_1);
x_279 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(x_1, x_250, x_273, x_274, x_275, x_276);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec_ref(x_279);
x_281 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_266, x_280);
if (lean_obj_tag(x_281) == 1)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
lean_inc(x_282);
x_283 = l_List_any___redArg(x_282, x_264);
if (x_283 == 0)
{
lean_object* x_284; 
lean_inc(x_282);
lean_inc(x_250);
lean_inc_ref(x_278);
lean_inc_ref(x_2);
x_284 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_2, x_255, x_278, x_250, x_282, x_265, x_267, x_268, x_269, x_270, x_271, x_272, x_273, x_274, x_275, x_276);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_282);
x_287 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_266, x_280, x_286);
x_29 = x_285;
x_30 = x_250;
x_31 = x_287;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_282);
lean_dec(x_280);
lean_dec_ref(x_278);
lean_dec_ref(x_266);
lean_dec(x_250);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_288 = lean_ctor_get(x_284, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_289 = x_284;
} else {
 lean_dec_ref(x_284);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 1, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_288);
return x_290;
}
}
else
{
lean_dec(x_282);
lean_dec(x_280);
lean_dec_ref(x_278);
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_255);
x_29 = x_265;
x_30 = x_250;
x_31 = x_266;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_281);
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec_ref(x_264);
lean_dec(x_255);
x_291 = lean_box(0);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_278);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_266, x_280, x_292);
x_29 = x_265;
x_30 = x_250;
x_31 = x_293;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec_ref(x_278);
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec(x_274);
lean_dec_ref(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec_ref(x_264);
lean_dec(x_255);
lean_dec(x_250);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_294 = lean_ctor_get(x_279, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_295 = x_279;
} else {
 lean_dec_ref(x_279);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_314 = lean_ctor_get(x_262, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_315 = x_262;
} else {
 lean_dec_ref(x_262);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_317 = lean_ctor_get(x_258, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_318 = x_258;
} else {
 lean_dec_ref(x_258);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_254);
if (lean_is_scalar(x_252)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_252;
}
lean_ctor_set(x_320, 0, x_250);
lean_ctor_set(x_320, 1, x_251);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_249);
lean_ctor_set(x_321, 1, x_320);
x_23 = x_321;
x_24 = lean_box(0);
goto block_28;
}
}
}
block_28:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_usize_add(x_10, x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_26, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_27;
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_30, x_33);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_23 = x_36;
x_24 = lean_box(0);
goto block_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___boxed(lean_object** _args) {
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
_start:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_24 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, size_t x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; lean_object* x_32; uint8_t x_38; 
x_38 = lean_usize_dec_lt(x_18, x_17);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; uint8_t x_51; uint8_t x_99; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_41 = x_19;
} else {
 lean_dec_ref(x_19);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_50 = lean_array_uget(x_16, x_18);
x_99 = l_Lean_Expr_isApp(x_50);
if (x_99 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isEq(x_50);
if (x_100 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
x_51 = x_15;
goto block_98;
}
}
block_47:
{
lean_object* x_46; 
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
block_49:
{
lean_object* x_48; 
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_31 = x_48;
x_32 = lean_box(0);
goto block_37;
}
block_98:
{
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isHEq(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_41);
lean_inc(x_50);
x_53 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_50, x_20, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_31 = x_56;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_57);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_50);
x_58 = lean_apply_12(x_57, x_50, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, lean_box(0));
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_getAppFn(x_50);
x_62 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_61, x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Meta_Grind_isCastLikeFn(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
lean_dec(x_44);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
x_68 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_68, x_70);
lean_dec(x_68);
lean_inc(x_50);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_69, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_43);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_size(x_72);
x_76 = 0;
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_2);
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_50, x_2, x_3, x_4, x_5, x_6, x_61, x_72, x_75, x_76, x_74, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_80);
x_31 = x_79;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_31 = x_84;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_50);
lean_dec(x_44);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_42);
lean_ctor_set(x_91, 1, x_43);
x_31 = x_91;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_92; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_53);
if (x_95 == 0)
{
return x_53;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_53, 0);
lean_inc(x_96);
lean_dec(x_53);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
}
}
}
block_37:
{
lean_object* x_33; size_t x_34; size_t x_35; 
lean_inc(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_18, x_34);
x_18 = x_35;
x_19 = x_33;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_15);
x_32 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_33 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31, x_16, x_32, x_33, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, size_t x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; lean_object* x_32; uint8_t x_38; 
x_38 = lean_usize_dec_lt(x_18, x_17);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; uint8_t x_51; uint8_t x_99; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_41 = x_19;
} else {
 lean_dec_ref(x_19);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_50 = lean_array_uget(x_16, x_18);
x_99 = l_Lean_Expr_isApp(x_50);
if (x_99 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isEq(x_50);
if (x_100 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
x_51 = x_14;
goto block_98;
}
}
block_47:
{
lean_object* x_46; 
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
block_49:
{
lean_object* x_48; 
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_31 = x_48;
x_32 = lean_box(0);
goto block_37;
}
block_98:
{
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isHEq(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_41);
lean_inc(x_50);
x_53 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_50, x_20, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_31 = x_56;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_57);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_50);
x_58 = lean_apply_12(x_57, x_50, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, lean_box(0));
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_getAppFn(x_50);
x_62 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_61, x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Meta_Grind_isCastLikeFn(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
lean_dec(x_44);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
x_68 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_68, x_70);
lean_dec(x_68);
lean_inc(x_50);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_69, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_43);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_size(x_72);
x_76 = 0;
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_1);
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_50, x_1, x_2, x_3, x_4, x_5, x_61, x_72, x_75, x_76, x_74, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_80);
x_31 = x_79;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_31 = x_84;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_50);
lean_dec(x_44);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_42);
lean_ctor_set(x_91, 1, x_43);
x_31 = x_91;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_92; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_53);
if (x_95 == 0)
{
return x_53;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_53, 0);
lean_inc(x_96);
lean_dec(x_53);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
}
}
}
block_37:
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
lean_inc(x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_18, x_34);
x_36 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19_spec__27(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_16, x_17, x_35, x_33, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_14);
x_32 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_33 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31, x_15, x_16, x_32, x_33, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_17);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_31, x_30, x_33, x_34, x_32, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_30);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 0);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_39);
lean_ctor_set(x_35, 0, x_16);
return x_35;
}
else
{
lean_object* x_40; 
lean_inc_ref(x_38);
lean_dec(x_37);
lean_free_object(x_16);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
lean_ctor_set(x_35, 0, x_40);
return x_35;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_16);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_42);
lean_dec(x_41);
lean_free_object(x_16);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_16);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_16, 0);
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_17);
x_53 = lean_array_size(x_50);
x_54 = 0;
x_55 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_51, x_50, x_53, x_54, x_52, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_50);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_56, 0);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_inc_ref(x_58);
lean_dec(x_56);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec_ref(x_58);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_17);
x_71 = lean_array_size(x_68);
x_72 = 0;
x_73 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_69, x_68, x_71, x_72, x_70, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_68);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_75, 0);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_ctor_set(x_16, 0, x_77);
lean_ctor_set(x_73, 0, x_16);
return x_73;
}
else
{
lean_object* x_78; 
lean_inc_ref(x_76);
lean_dec(x_75);
lean_free_object(x_16);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec_ref(x_76);
lean_ctor_set(x_73, 0, x_78);
return x_73;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_ctor_get(x_79, 0);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_ctor_set(x_16, 0, x_81);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_16);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_inc_ref(x_80);
lean_dec(x_79);
lean_free_object(x_16);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec_ref(x_80);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_16);
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_16, 0);
lean_inc(x_88);
lean_dec(x_16);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_17);
x_91 = lean_array_size(x_88);
x_92 = 0;
x_93 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_89, x_88, x_91, x_92, x_90, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_88);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_94, 0);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_inc_ref(x_96);
lean_dec(x_94);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec_ref(x_96);
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_95;
}
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_93, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_103 = x_93;
} else {
 lean_dec_ref(x_93);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, size_t x_18, size_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
uint8_t x_32; 
x_32 = lean_usize_dec_lt(x_19, x_18);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_20, 1);
x_36 = lean_ctor_get(x_20, 0);
lean_dec(x_36);
x_37 = lean_array_uget(x_17, x_19);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_35);
lean_inc_ref(x_1);
x_38 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_37, x_35, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_20, 0, x_41);
lean_ctor_set(x_38, 0, x_20);
return x_38;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; 
lean_free_object(x_38);
lean_dec(x_35);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec_ref(x_40);
lean_inc(x_16);
lean_ctor_set(x_20, 1, x_42);
lean_ctor_set(x_20, 0, x_16);
x_43 = 1;
x_44 = lean_usize_add(x_19, x_43);
x_19 = x_44;
goto _start;
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_20, 0, x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_20);
return x_48;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_35);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec_ref(x_46);
lean_inc(x_16);
lean_ctor_set(x_20, 1, x_49);
lean_ctor_set(x_20, 0, x_16);
x_50 = 1;
x_51 = lean_usize_add(x_19, x_50);
x_19 = x_51;
goto _start;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_20);
lean_dec(x_35);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_dec(x_20);
x_57 = lean_array_uget(x_17, x_19);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_56);
lean_inc_ref(x_1);
x_58 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_57, x_56, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; 
lean_dec(x_60);
lean_dec(x_56);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec_ref(x_59);
lean_inc(x_16);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_16);
lean_ctor_set(x_65, 1, x_64);
x_66 = 1;
x_67 = lean_usize_add(x_19, x_66);
x_19 = x_67;
x_20 = x_65;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_70 = x_58;
} else {
 lean_dec_ref(x_58);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_32 = lean_unbox(x_14);
x_33 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_34 = lean_unbox_usize(x_19);
lean_dec(x_19);
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32, x_15, x_16, x_17, x_33, x_34, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_29; lean_object* x_30; 
x_29 = lean_unbox(x_14);
x_30 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_30;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, size_t x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; lean_object* x_32; uint8_t x_38; 
x_38 = lean_usize_dec_lt(x_18, x_17);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; uint8_t x_51; uint8_t x_99; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_41 = x_19;
} else {
 lean_dec_ref(x_19);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_50 = lean_array_uget(x_16, x_18);
x_99 = l_Lean_Expr_isApp(x_50);
if (x_99 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isEq(x_50);
if (x_100 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
x_51 = x_15;
goto block_98;
}
}
block_47:
{
lean_object* x_46; 
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
block_49:
{
lean_object* x_48; 
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_31 = x_48;
x_32 = lean_box(0);
goto block_37;
}
block_98:
{
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isHEq(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_41);
lean_inc(x_50);
x_53 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_50, x_20, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_31 = x_56;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_57);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_50);
x_58 = lean_apply_12(x_57, x_50, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, lean_box(0));
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_getAppFn(x_50);
x_62 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_61, x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Meta_Grind_isCastLikeFn(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
lean_dec(x_44);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
x_68 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_68, x_70);
lean_dec(x_68);
lean_inc(x_50);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_69, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_43);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_size(x_72);
x_76 = 0;
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_2);
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_50, x_2, x_3, x_4, x_5, x_6, x_61, x_72, x_75, x_76, x_74, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_80);
x_31 = x_79;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_31 = x_84;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_50);
lean_dec(x_44);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_42);
lean_ctor_set(x_91, 1, x_43);
x_31 = x_91;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_92; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_53);
if (x_95 == 0)
{
return x_53;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_53, 0);
lean_inc(x_96);
lean_dec(x_53);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
}
}
}
block_37:
{
lean_object* x_33; size_t x_34; size_t x_35; 
lean_inc(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_18, x_34);
x_18 = x_35;
x_19 = x_33;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_15);
x_32 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_33 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31, x_16, x_32, x_33, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, size_t x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; lean_object* x_32; uint8_t x_38; 
x_38 = lean_usize_dec_lt(x_18, x_17);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; uint8_t x_51; uint8_t x_99; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_41 = x_19;
} else {
 lean_dec_ref(x_19);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_50 = lean_array_uget(x_16, x_18);
x_99 = l_Lean_Expr_isApp(x_50);
if (x_99 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isEq(x_50);
if (x_100 == 0)
{
x_51 = x_99;
goto block_98;
}
else
{
x_51 = x_14;
goto block_98;
}
}
block_47:
{
lean_object* x_46; 
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_31 = x_46;
x_32 = lean_box(0);
goto block_37;
}
block_49:
{
lean_object* x_48; 
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_31 = x_48;
x_32 = lean_box(0);
goto block_37;
}
block_98:
{
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isHEq(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_41);
lean_inc(x_50);
x_53 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_50, x_20, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_31 = x_56;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_57);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_50);
x_58 = lean_apply_12(x_57, x_50, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, lean_box(0));
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_getAppFn(x_50);
x_62 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___redArg(x_61, x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Meta_Grind_isCastLikeFn(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
lean_dec(x_44);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
x_68 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_68, x_70);
lean_dec(x_68);
lean_inc(x_50);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_69, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_43);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_size(x_72);
x_76 = 0;
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_1);
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_50, x_1, x_2, x_3, x_4, x_5, x_61, x_72, x_75, x_76, x_74, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_80);
x_31 = x_79;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_31 = x_84;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_50);
x_45 = lean_box(0);
goto block_47;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_50);
lean_dec(x_44);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_42);
lean_ctor_set(x_91, 1, x_43);
x_31 = x_91;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_92; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_53);
if (x_95 == 0)
{
return x_53;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_53, 0);
lean_inc(x_96);
lean_dec(x_53);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_44);
goto block_49;
}
}
}
}
block_37:
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
lean_inc(x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_18, x_34);
x_36 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16_spec__21(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_16, x_17, x_35, x_33, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_14);
x_32 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_33 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31, x_15, x_16, x_32, x_33, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26) {
_start:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_15);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_1);
x_30 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_16, x_28, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_16);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
lean_free_object(x_30);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_size(x_29);
x_38 = 0;
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_35, x_29, x_37, x_38, x_36, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_29);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; 
lean_inc_ref(x_42);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_45, 0);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_inc_ref(x_46);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
lean_dec(x_30);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec_ref(x_54);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_array_size(x_29);
x_61 = 0;
x_62 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_58, x_29, x_60, x_61, x_59, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_63, 0);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_65);
lean_dec(x_63);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec_ref(x_65);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_30);
if (x_73 == 0)
{
return x_30;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_30, 0);
lean_inc(x_74);
lean_dec(x_30);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_28; lean_object* x_29; 
x_28 = lean_unbox(x_14);
x_29 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_29;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mbtc___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mbtc___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*10 + 17);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
x_18 = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(x_2, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_free_object(x_18);
x_22 = lean_st_ref_get(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__2));
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0));
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0));
x_29 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
x_30 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__4));
x_31 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
x_32 = l_Lean_Meta_Grind_mbtc___closed__6;
x_33 = lean_unbox(x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(x_1, x_29, x_30, x_27, x_28, x_26, x_31, x_26, x_31, x_26, x_31, x_31, x_26, x_33, x_24, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_nat_dec_eq(x_39, x_25);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_34);
lean_dec(x_20);
x_42 = lean_st_ref_get(x_2);
x_43 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_94; uint8_t x_101; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_42, 0);
x_103 = lean_ctor_get(x_42, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_102, 15);
lean_inc_ref(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_44, 0);
lean_inc(x_105);
lean_dec(x_44);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = lean_nat_dec_lt(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_free_object(x_42);
lean_free_object(x_37);
x_108 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
x_109 = lean_array_get_size(x_40);
x_110 = lean_nat_dec_lt(x_25, x_109);
if (x_110 == 0)
{
lean_dec_ref(x_40);
x_94 = x_108;
goto block_100;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
if (x_110 == 0)
{
lean_dec_ref(x_40);
x_94 = x_108;
goto block_100;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
x_112 = 0;
x_113 = lean_usize_of_nat(x_109);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_40, x_112, x_113, x_108);
lean_dec_ref(x_40);
x_94 = x_114;
goto block_100;
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = 0;
x_116 = lean_usize_of_nat(x_109);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_40, x_115, x_116, x_108);
lean_dec_ref(x_40);
x_94 = x_117;
goto block_100;
}
}
}
else
{
lean_object* x_118; 
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_118 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get_uint8(x_120, sizeof(void*)*10 + 14);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_free_object(x_42);
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_122 = lean_box(x_41);
lean_ctor_set(x_118, 0, x_122);
return x_118;
}
else
{
lean_object* x_123; 
lean_free_object(x_118);
x_123 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_Meta_Grind_mbtc___closed__8;
x_127 = l_Nat_reprFast(x_125);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_MessageData_ofFormat(x_128);
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_129);
lean_ctor_set(x_42, 0, x_126);
x_130 = l_Lean_Meta_Grind_mbtc___closed__10;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_130);
lean_ctor_set(x_37, 0, x_42);
x_131 = l_Lean_Meta_Grind_reportIssue(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_dec(x_133);
x_134 = lean_box(x_41);
lean_ctor_set(x_131, 0, x_134);
return x_131;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_131);
x_135 = lean_box(x_41);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_131);
if (x_137 == 0)
{
return x_131;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
lean_dec(x_131);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_free_object(x_42);
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
return x_123;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_123, 0);
lean_inc(x_141);
lean_dec(x_123);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_118, 0);
lean_inc(x_143);
lean_dec(x_118);
x_144 = lean_ctor_get_uint8(x_143, sizeof(void*)*10 + 14);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_free_object(x_42);
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_145 = lean_box(x_41);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
else
{
lean_object* x_147; 
x_147 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_Meta_Grind_mbtc___closed__8;
x_151 = l_Nat_reprFast(x_149);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = l_Lean_MessageData_ofFormat(x_152);
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_153);
lean_ctor_set(x_42, 0, x_150);
x_154 = l_Lean_Meta_Grind_mbtc___closed__10;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_154);
lean_ctor_set(x_37, 0, x_42);
x_155 = l_Lean_Meta_Grind_reportIssue(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(x_41);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_free_object(x_42);
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_162 = lean_ctor_get(x_147, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_163 = x_147;
} else {
 lean_dec_ref(x_147);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_free_object(x_42);
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_118);
if (x_165 == 0)
{
return x_118;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_118, 0);
lean_inc(x_166);
lean_dec(x_118);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_168 = lean_ctor_get(x_42, 0);
lean_inc(x_168);
lean_dec(x_42);
x_169 = lean_ctor_get(x_168, 15);
lean_inc_ref(x_169);
lean_dec_ref(x_168);
x_170 = lean_ctor_get(x_44, 0);
lean_inc(x_170);
lean_dec(x_44);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_nat_dec_lt(x_170, x_171);
lean_dec(x_171);
lean_dec(x_170);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_free_object(x_37);
x_173 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
x_174 = lean_array_get_size(x_40);
x_175 = lean_nat_dec_lt(x_25, x_174);
if (x_175 == 0)
{
lean_dec_ref(x_40);
x_94 = x_173;
goto block_100;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_174, x_174);
if (x_176 == 0)
{
if (x_175 == 0)
{
lean_dec_ref(x_40);
x_94 = x_173;
goto block_100;
}
else
{
size_t x_177; size_t x_178; lean_object* x_179; 
x_177 = 0;
x_178 = lean_usize_of_nat(x_174);
x_179 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_40, x_177, x_178, x_173);
lean_dec_ref(x_40);
x_94 = x_179;
goto block_100;
}
}
else
{
size_t x_180; size_t x_181; lean_object* x_182; 
x_180 = 0;
x_181 = lean_usize_of_nat(x_174);
x_182 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_40, x_180, x_181, x_173);
lean_dec_ref(x_40);
x_94 = x_182;
goto block_100;
}
}
}
else
{
lean_object* x_183; 
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_183 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get_uint8(x_184, sizeof(void*)*10 + 14);
lean_dec(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_187 = lean_box(x_41);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(0, 1, 0);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
else
{
lean_object* x_189; 
lean_dec(x_185);
x_189 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Meta_Grind_mbtc___closed__8;
x_193 = l_Nat_reprFast(x_191);
x_194 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Lean_MessageData_ofFormat(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_Meta_Grind_mbtc___closed__10;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_197);
lean_ctor_set(x_37, 0, x_196);
x_198 = l_Lean_Meta_Grind_reportIssue(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_199 = x_198;
} else {
 lean_dec_ref(x_198);
 x_199 = lean_box(0);
}
x_200 = lean_box(x_41);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_205 = lean_ctor_get(x_189, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_206 = x_189;
} else {
 lean_dec_ref(x_189);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_free_object(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_208 = lean_ctor_get(x_183, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_209 = x_183;
} else {
 lean_dec_ref(x_183);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
}
block_81:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_array_get_size(x_45);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_45, x_25, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_45);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Array_isEmpty___redArg(x_49);
if (x_50 == 0)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
lean_free_object(x_47);
x_51 = lean_box(0);
x_52 = lean_array_size(x_49);
x_53 = 0;
x_54 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_51, x_49, x_52, x_53, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_49);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(x_16);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
x_58 = lean_box(x_16);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_box(x_41);
lean_ctor_set(x_47, 0, x_63);
return x_47;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_47, 0);
lean_inc(x_64);
lean_dec(x_47);
x_65 = l_Array_isEmpty___redArg(x_64);
if (x_65 == 0)
{
lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_array_size(x_64);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_66, x_64, x_67, x_68, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_70 = x_69;
} else {
 lean_dec_ref(x_69);
 x_70 = lean_box(0);
}
x_71 = lean_box(x_16);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_box(x_41);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_47);
if (x_78 == 0)
{
return x_47;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_47, 0);
lean_inc(x_79);
lean_dec(x_47);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
block_87:
{
lean_object* x_86; 
lean_dec(x_82);
x_86 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_84, x_83, x_85);
lean_dec(x_85);
x_45 = x_86;
goto block_81;
}
block_93:
{
uint8_t x_92; 
x_92 = lean_nat_dec_le(x_91, x_88);
if (x_92 == 0)
{
lean_dec(x_88);
lean_inc(x_91);
x_82 = x_89;
x_83 = x_91;
x_84 = x_90;
x_85 = x_91;
goto block_87;
}
else
{
x_82 = x_89;
x_83 = x_91;
x_84 = x_90;
x_85 = x_88;
goto block_87;
}
}
block_100:
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_eq(x_95, x_25);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_95, x_97);
x_99 = lean_nat_dec_le(x_25, x_98);
if (x_99 == 0)
{
lean_inc(x_98);
x_88 = x_98;
x_89 = x_95;
x_90 = x_94;
x_91 = x_98;
goto block_93;
}
else
{
x_88 = x_98;
x_89 = x_95;
x_90 = x_94;
x_91 = x_25;
goto block_93;
}
}
else
{
x_45 = x_94;
goto block_81;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_42);
lean_free_object(x_37);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_43);
if (x_211 == 0)
{
return x_43;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_43, 0);
lean_inc(x_212);
lean_dec(x_43);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
lean_free_object(x_37);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_34, 0, x_20);
return x_34;
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_37, 0);
x_215 = lean_ctor_get(x_37, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_37);
x_216 = lean_nat_dec_eq(x_214, x_25);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_free_object(x_34);
lean_dec(x_20);
x_217 = lean_st_ref_get(x_2);
x_218 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_254; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_261 = lean_ctor_get(x_217, 0);
lean_inc_ref(x_261);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_262 = x_217;
} else {
 lean_dec_ref(x_217);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_261, 15);
lean_inc_ref(x_263);
lean_dec_ref(x_261);
x_264 = lean_ctor_get(x_219, 0);
lean_inc(x_264);
lean_dec(x_219);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
lean_dec_ref(x_263);
x_266 = lean_nat_dec_lt(x_264, x_265);
lean_dec(x_265);
lean_dec(x_264);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_262);
x_267 = lean_mk_empty_array_with_capacity(x_214);
lean_dec(x_214);
x_268 = lean_array_get_size(x_215);
x_269 = lean_nat_dec_lt(x_25, x_268);
if (x_269 == 0)
{
lean_dec_ref(x_215);
x_254 = x_267;
goto block_260;
}
else
{
uint8_t x_270; 
x_270 = lean_nat_dec_le(x_268, x_268);
if (x_270 == 0)
{
if (x_269 == 0)
{
lean_dec_ref(x_215);
x_254 = x_267;
goto block_260;
}
else
{
size_t x_271; size_t x_272; lean_object* x_273; 
x_271 = 0;
x_272 = lean_usize_of_nat(x_268);
x_273 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_215, x_271, x_272, x_267);
lean_dec_ref(x_215);
x_254 = x_273;
goto block_260;
}
}
else
{
size_t x_274; size_t x_275; lean_object* x_276; 
x_274 = 0;
x_275 = lean_usize_of_nat(x_268);
x_276 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_215, x_274, x_275, x_267);
lean_dec_ref(x_215);
x_254 = x_276;
goto block_260;
}
}
}
else
{
lean_object* x_277; 
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_2);
x_277 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get_uint8(x_278, sizeof(void*)*10 + 14);
lean_dec(x_278);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_281 = lean_box(x_216);
if (lean_is_scalar(x_279)) {
 x_282 = lean_alloc_ctor(0, 1, 0);
} else {
 x_282 = x_279;
}
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
else
{
lean_object* x_283; 
lean_dec(x_279);
x_283 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec_ref(x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec(x_284);
x_286 = l_Lean_Meta_Grind_mbtc___closed__8;
x_287 = l_Nat_reprFast(x_285);
x_288 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = l_Lean_MessageData_ofFormat(x_288);
if (lean_is_scalar(x_262)) {
 x_290 = lean_alloc_ctor(7, 2, 0);
} else {
 x_290 = x_262;
 lean_ctor_set_tag(x_290, 7);
}
lean_ctor_set(x_290, 0, x_286);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Lean_Meta_Grind_mbtc___closed__10;
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_Meta_Grind_reportIssue(x_292, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_294 = x_293;
} else {
 lean_dec_ref(x_293);
 x_294 = lean_box(0);
}
x_295 = lean_box(x_216);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_293, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_298 = x_293;
} else {
 lean_dec_ref(x_293);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_300 = lean_ctor_get(x_283, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_301 = x_283;
} else {
 lean_dec_ref(x_283);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_303 = lean_ctor_get(x_277, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_304 = x_277;
} else {
 lean_dec_ref(x_277);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
return x_305;
}
}
block_241:
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_array_get_size(x_220);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_222 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_220, x_25, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = l_Array_isEmpty___redArg(x_223);
if (x_225 == 0)
{
lean_object* x_226; size_t x_227; size_t x_228; lean_object* x_229; 
lean_dec(x_224);
x_226 = lean_box(0);
x_227 = lean_array_size(x_223);
x_228 = 0;
x_229 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_226, x_223, x_227, x_228, x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_223);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_230 = x_229;
} else {
 lean_dec_ref(x_229);
 x_230 = lean_box(0);
}
x_231 = lean_box(x_16);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_234 = x_229;
} else {
 lean_dec_ref(x_229);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_236 = lean_box(x_216);
if (lean_is_scalar(x_224)) {
 x_237 = lean_alloc_ctor(0, 1, 0);
} else {
 x_237 = x_224;
}
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = lean_ctor_get(x_222, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_239 = x_222;
} else {
 lean_dec_ref(x_222);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
block_247:
{
lean_object* x_246; 
lean_dec(x_242);
x_246 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_244, x_243, x_245);
lean_dec(x_245);
x_220 = x_246;
goto block_241;
}
block_253:
{
uint8_t x_252; 
x_252 = lean_nat_dec_le(x_251, x_248);
if (x_252 == 0)
{
lean_dec(x_248);
lean_inc(x_251);
x_242 = x_249;
x_243 = x_251;
x_244 = x_250;
x_245 = x_251;
goto block_247;
}
else
{
x_242 = x_249;
x_243 = x_251;
x_244 = x_250;
x_245 = x_248;
goto block_247;
}
}
block_260:
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_array_get_size(x_254);
x_256 = lean_nat_dec_eq(x_255, x_25);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_nat_sub(x_255, x_257);
x_259 = lean_nat_dec_le(x_25, x_258);
if (x_259 == 0)
{
lean_inc(x_258);
x_248 = x_258;
x_249 = x_255;
x_250 = x_254;
x_251 = x_258;
goto block_253;
}
else
{
x_248 = x_258;
x_249 = x_255;
x_250 = x_254;
x_251 = x_25;
goto block_253;
}
}
else
{
x_220 = x_254;
goto block_241;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_306 = lean_ctor_get(x_218, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_307 = x_218;
} else {
 lean_dec_ref(x_218);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
return x_308;
}
}
else
{
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_34, 0, x_20);
return x_34;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_34, 0);
lean_inc(x_309);
lean_dec(x_34);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc_ref(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = lean_nat_dec_eq(x_311, x_25);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_20);
x_315 = lean_st_ref_get(x_2);
x_316 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_352; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
lean_dec_ref(x_316);
x_359 = lean_ctor_get(x_315, 0);
lean_inc_ref(x_359);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_360 = x_315;
} else {
 lean_dec_ref(x_315);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_359, 15);
lean_inc_ref(x_361);
lean_dec_ref(x_359);
x_362 = lean_ctor_get(x_317, 0);
lean_inc(x_362);
lean_dec(x_317);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
lean_dec_ref(x_361);
x_364 = lean_nat_dec_lt(x_362, x_363);
lean_dec(x_363);
lean_dec(x_362);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
lean_dec(x_360);
lean_dec(x_313);
x_365 = lean_mk_empty_array_with_capacity(x_311);
lean_dec(x_311);
x_366 = lean_array_get_size(x_312);
x_367 = lean_nat_dec_lt(x_25, x_366);
if (x_367 == 0)
{
lean_dec_ref(x_312);
x_352 = x_365;
goto block_358;
}
else
{
uint8_t x_368; 
x_368 = lean_nat_dec_le(x_366, x_366);
if (x_368 == 0)
{
if (x_367 == 0)
{
lean_dec_ref(x_312);
x_352 = x_365;
goto block_358;
}
else
{
size_t x_369; size_t x_370; lean_object* x_371; 
x_369 = 0;
x_370 = lean_usize_of_nat(x_366);
x_371 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_312, x_369, x_370, x_365);
lean_dec_ref(x_312);
x_352 = x_371;
goto block_358;
}
}
else
{
size_t x_372; size_t x_373; lean_object* x_374; 
x_372 = 0;
x_373 = lean_usize_of_nat(x_366);
x_374 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_312, x_372, x_373, x_365);
lean_dec_ref(x_312);
x_352 = x_374;
goto block_358;
}
}
}
else
{
lean_object* x_375; 
lean_dec_ref(x_312);
lean_dec(x_311);
lean_dec(x_2);
x_375 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get_uint8(x_376, sizeof(void*)*10 + 14);
lean_dec(x_376);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_360);
lean_dec(x_313);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_379 = lean_box(x_314);
if (lean_is_scalar(x_377)) {
 x_380 = lean_alloc_ctor(0, 1, 0);
} else {
 x_380 = x_377;
}
lean_ctor_set(x_380, 0, x_379);
return x_380;
}
else
{
lean_object* x_381; 
lean_dec(x_377);
x_381 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec(x_382);
x_384 = l_Lean_Meta_Grind_mbtc___closed__8;
x_385 = l_Nat_reprFast(x_383);
x_386 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_386, 0, x_385);
x_387 = l_Lean_MessageData_ofFormat(x_386);
if (lean_is_scalar(x_360)) {
 x_388 = lean_alloc_ctor(7, 2, 0);
} else {
 x_388 = x_360;
 lean_ctor_set_tag(x_388, 7);
}
lean_ctor_set(x_388, 0, x_384);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_Meta_Grind_mbtc___closed__10;
if (lean_is_scalar(x_313)) {
 x_390 = lean_alloc_ctor(7, 2, 0);
} else {
 x_390 = x_313;
 lean_ctor_set_tag(x_390, 7);
}
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_Meta_Grind_reportIssue(x_390, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 x_392 = x_391;
} else {
 lean_dec_ref(x_391);
 x_392 = lean_box(0);
}
x_393 = lean_box(x_314);
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(0, 1, 0);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_391, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 x_396 = x_391;
} else {
 lean_dec_ref(x_391);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_360);
lean_dec(x_313);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_398 = lean_ctor_get(x_381, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_399 = x_381;
} else {
 lean_dec_ref(x_381);
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
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_360);
lean_dec(x_313);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_401 = lean_ctor_get(x_375, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_402 = x_375;
} else {
 lean_dec_ref(x_375);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
return x_403;
}
}
block_339:
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_array_get_size(x_318);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_320 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_318, x_25, x_319, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
x_323 = l_Array_isEmpty___redArg(x_321);
if (x_323 == 0)
{
lean_object* x_324; size_t x_325; size_t x_326; lean_object* x_327; 
lean_dec(x_322);
x_324 = lean_box(0);
x_325 = lean_array_size(x_321);
x_326 = 0;
x_327 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_324, x_321, x_325, x_326, x_324, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_321);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_328 = x_327;
} else {
 lean_dec_ref(x_327);
 x_328 = lean_box(0);
}
x_329 = lean_box(x_16);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 1, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_327, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_332 = x_327;
} else {
 lean_dec_ref(x_327);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 1, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_331);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_321);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_334 = lean_box(x_314);
if (lean_is_scalar(x_322)) {
 x_335 = lean_alloc_ctor(0, 1, 0);
} else {
 x_335 = x_322;
}
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_336 = lean_ctor_get(x_320, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_337 = x_320;
} else {
 lean_dec_ref(x_320);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
}
block_345:
{
lean_object* x_344; 
lean_dec(x_340);
x_344 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_342, x_341, x_343);
lean_dec(x_343);
x_318 = x_344;
goto block_339;
}
block_351:
{
uint8_t x_350; 
x_350 = lean_nat_dec_le(x_349, x_346);
if (x_350 == 0)
{
lean_dec(x_346);
lean_inc(x_349);
x_340 = x_347;
x_341 = x_349;
x_342 = x_348;
x_343 = x_349;
goto block_345;
}
else
{
x_340 = x_347;
x_341 = x_349;
x_342 = x_348;
x_343 = x_346;
goto block_345;
}
}
block_358:
{
lean_object* x_353; uint8_t x_354; 
x_353 = lean_array_get_size(x_352);
x_354 = lean_nat_dec_eq(x_353, x_25);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_nat_sub(x_353, x_355);
x_357 = lean_nat_dec_le(x_25, x_356);
if (x_357 == 0)
{
lean_inc(x_356);
x_346 = x_356;
x_347 = x_353;
x_348 = x_352;
x_349 = x_356;
goto block_351;
}
else
{
x_346 = x_356;
x_347 = x_353;
x_348 = x_352;
x_349 = x_25;
goto block_351;
}
}
else
{
x_318 = x_352;
goto block_339;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_315);
lean_dec(x_313);
lean_dec_ref(x_312);
lean_dec(x_311);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_404 = lean_ctor_get(x_316, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_405 = x_316;
} else {
 lean_dec_ref(x_316);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_404);
return x_406;
}
}
else
{
lean_object* x_407; 
lean_dec(x_313);
lean_dec_ref(x_312);
lean_dec(x_311);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_407 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_407, 0, x_20);
return x_407;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_408 = !lean_is_exclusive(x_34);
if (x_408 == 0)
{
return x_34;
}
else
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_34, 0);
lean_inc(x_409);
lean_dec(x_34);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
return x_410;
}
}
}
else
{
uint8_t x_411; lean_object* x_412; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_411 = 0;
x_412 = lean_box(x_411);
lean_ctor_set(x_18, 0, x_412);
return x_18;
}
}
else
{
lean_object* x_413; uint8_t x_414; 
x_413 = lean_ctor_get(x_18, 0);
lean_inc(x_413);
lean_dec(x_18);
x_414 = lean_unbox(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; 
x_415 = lean_st_ref_get(x_2);
x_416 = lean_ctor_get(x_415, 0);
lean_inc_ref(x_416);
lean_dec(x_415);
x_417 = lean_ctor_get(x_416, 3);
lean_inc_ref(x_417);
lean_dec_ref(x_416);
x_418 = lean_unsigned_to_nat(0u);
x_419 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__2));
x_420 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0));
x_421 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0));
x_422 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
x_423 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__4));
x_424 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
x_425 = l_Lean_Meta_Grind_mbtc___closed__6;
x_426 = lean_unbox(x_413);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_427 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(x_1, x_422, x_423, x_420, x_421, x_419, x_424, x_419, x_424, x_419, x_424, x_424, x_419, x_426, x_417, x_425, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc_ref(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
x_434 = lean_nat_dec_eq(x_431, x_418);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_429);
lean_dec(x_413);
x_435 = lean_st_ref_get(x_2);
x_436 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_472; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_479 = lean_ctor_get(x_435, 0);
lean_inc_ref(x_479);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_480 = x_435;
} else {
 lean_dec_ref(x_435);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_479, 15);
lean_inc_ref(x_481);
lean_dec_ref(x_479);
x_482 = lean_ctor_get(x_437, 0);
lean_inc(x_482);
lean_dec(x_437);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec_ref(x_481);
x_484 = lean_nat_dec_lt(x_482, x_483);
lean_dec(x_483);
lean_dec(x_482);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_dec(x_480);
lean_dec(x_433);
x_485 = lean_mk_empty_array_with_capacity(x_431);
lean_dec(x_431);
x_486 = lean_array_get_size(x_432);
x_487 = lean_nat_dec_lt(x_418, x_486);
if (x_487 == 0)
{
lean_dec_ref(x_432);
x_472 = x_485;
goto block_478;
}
else
{
uint8_t x_488; 
x_488 = lean_nat_dec_le(x_486, x_486);
if (x_488 == 0)
{
if (x_487 == 0)
{
lean_dec_ref(x_432);
x_472 = x_485;
goto block_478;
}
else
{
size_t x_489; size_t x_490; lean_object* x_491; 
x_489 = 0;
x_490 = lean_usize_of_nat(x_486);
x_491 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_432, x_489, x_490, x_485);
lean_dec_ref(x_432);
x_472 = x_491;
goto block_478;
}
}
else
{
size_t x_492; size_t x_493; lean_object* x_494; 
x_492 = 0;
x_493 = lean_usize_of_nat(x_486);
x_494 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_432, x_492, x_493, x_485);
lean_dec_ref(x_432);
x_472 = x_494;
goto block_478;
}
}
}
else
{
lean_object* x_495; 
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_2);
x_495 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; uint8_t x_498; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get_uint8(x_496, sizeof(void*)*10 + 14);
lean_dec(x_496);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_480);
lean_dec(x_433);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_499 = lean_box(x_434);
if (lean_is_scalar(x_497)) {
 x_500 = lean_alloc_ctor(0, 1, 0);
} else {
 x_500 = x_497;
}
lean_ctor_set(x_500, 0, x_499);
return x_500;
}
else
{
lean_object* x_501; 
lean_dec(x_497);
x_501 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec_ref(x_501);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
lean_dec(x_502);
x_504 = l_Lean_Meta_Grind_mbtc___closed__8;
x_505 = l_Nat_reprFast(x_503);
x_506 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_506, 0, x_505);
x_507 = l_Lean_MessageData_ofFormat(x_506);
if (lean_is_scalar(x_480)) {
 x_508 = lean_alloc_ctor(7, 2, 0);
} else {
 x_508 = x_480;
 lean_ctor_set_tag(x_508, 7);
}
lean_ctor_set(x_508, 0, x_504);
lean_ctor_set(x_508, 1, x_507);
x_509 = l_Lean_Meta_Grind_mbtc___closed__10;
if (lean_is_scalar(x_433)) {
 x_510 = lean_alloc_ctor(7, 2, 0);
} else {
 x_510 = x_433;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
x_511 = l_Lean_Meta_Grind_reportIssue(x_510, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_512 = x_511;
} else {
 lean_dec_ref(x_511);
 x_512 = lean_box(0);
}
x_513 = lean_box(x_434);
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(0, 1, 0);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_513);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_511, 0);
lean_inc(x_515);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_516 = x_511;
} else {
 lean_dec_ref(x_511);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 1, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_515);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_480);
lean_dec(x_433);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_518 = lean_ctor_get(x_501, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 x_519 = x_501;
} else {
 lean_dec_ref(x_501);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_518);
return x_520;
}
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_480);
lean_dec(x_433);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_521 = lean_ctor_get(x_495, 0);
lean_inc(x_521);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_522 = x_495;
} else {
 lean_dec_ref(x_495);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 1, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_521);
return x_523;
}
}
block_459:
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_array_get_size(x_438);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_440 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_438, x_418, x_439, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_438);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
x_443 = l_Array_isEmpty___redArg(x_441);
if (x_443 == 0)
{
lean_object* x_444; size_t x_445; size_t x_446; lean_object* x_447; 
lean_dec(x_442);
x_444 = lean_box(0);
x_445 = lean_array_size(x_441);
x_446 = 0;
x_447 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_444, x_441, x_445, x_446, x_444, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_441);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 x_448 = x_447;
} else {
 lean_dec_ref(x_447);
 x_448 = lean_box(0);
}
x_449 = lean_box(x_16);
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(0, 1, 0);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_447, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 x_452 = x_447;
} else {
 lean_dec_ref(x_447);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_441);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_454 = lean_box(x_434);
if (lean_is_scalar(x_442)) {
 x_455 = lean_alloc_ctor(0, 1, 0);
} else {
 x_455 = x_442;
}
lean_ctor_set(x_455, 0, x_454);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_456 = lean_ctor_get(x_440, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_457 = x_440;
} else {
 lean_dec_ref(x_440);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
block_465:
{
lean_object* x_464; 
lean_dec(x_460);
x_464 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_462, x_461, x_463);
lean_dec(x_463);
x_438 = x_464;
goto block_459;
}
block_471:
{
uint8_t x_470; 
x_470 = lean_nat_dec_le(x_469, x_466);
if (x_470 == 0)
{
lean_dec(x_466);
lean_inc(x_469);
x_460 = x_467;
x_461 = x_469;
x_462 = x_468;
x_463 = x_469;
goto block_465;
}
else
{
x_460 = x_467;
x_461 = x_469;
x_462 = x_468;
x_463 = x_466;
goto block_465;
}
}
block_478:
{
lean_object* x_473; uint8_t x_474; 
x_473 = lean_array_get_size(x_472);
x_474 = lean_nat_dec_eq(x_473, x_418);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_sub(x_473, x_475);
x_477 = lean_nat_dec_le(x_418, x_476);
if (x_477 == 0)
{
lean_inc(x_476);
x_466 = x_476;
x_467 = x_473;
x_468 = x_472;
x_469 = x_476;
goto block_471;
}
else
{
x_466 = x_476;
x_467 = x_473;
x_468 = x_472;
x_469 = x_418;
goto block_471;
}
}
else
{
x_438 = x_472;
goto block_459;
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_435);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_524 = lean_ctor_get(x_436, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_525 = x_436;
} else {
 lean_dec_ref(x_436);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(1, 1, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_524);
return x_526;
}
}
else
{
lean_object* x_527; 
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_429)) {
 x_527 = lean_alloc_ctor(0, 1, 0);
} else {
 x_527 = x_429;
}
lean_ctor_set(x_527, 0, x_413);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_413);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_528 = lean_ctor_get(x_427, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_529 = x_427;
} else {
 lean_dec_ref(x_427);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_528);
return x_530;
}
}
else
{
uint8_t x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_413);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_531 = 0;
x_532 = lean_box(x_531);
x_533 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_533, 0, x_532);
return x_533;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
lean_object* x_534; uint8_t x_535; 
x_534 = lean_ctor_get(x_13, 0);
lean_inc(x_534);
lean_dec(x_13);
x_535 = lean_ctor_get_uint8(x_534, sizeof(void*)*10 + 17);
lean_dec(x_534);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_536 = lean_box(x_535);
x_537 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_537, 0, x_536);
return x_537;
}
else
{
lean_object* x_538; 
x_538 = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(x_2, x_4);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 x_540 = x_538;
} else {
 lean_dec_ref(x_538);
 x_540 = lean_box(0);
}
x_541 = lean_unbox(x_539);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; 
lean_dec(x_540);
x_542 = lean_st_ref_get(x_2);
x_543 = lean_ctor_get(x_542, 0);
lean_inc_ref(x_543);
lean_dec(x_542);
x_544 = lean_ctor_get(x_543, 3);
lean_inc_ref(x_544);
lean_dec_ref(x_543);
x_545 = lean_unsigned_to_nat(0u);
x_546 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__2));
x_547 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0));
x_548 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0));
x_549 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
x_550 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__4));
x_551 = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
x_552 = l_Lean_Meta_Grind_mbtc___closed__6;
x_553 = lean_unbox(x_539);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_554 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(x_1, x_549, x_550, x_547, x_548, x_546, x_551, x_546, x_551, x_546, x_551, x_551, x_546, x_553, x_544, x_552, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 x_556 = x_554;
} else {
 lean_dec_ref(x_554);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_555, 0);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc_ref(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
x_561 = lean_nat_dec_eq(x_558, x_545);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; 
lean_dec(x_556);
lean_dec(x_539);
x_562 = lean_st_ref_get(x_2);
x_563 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_599; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_606 = lean_ctor_get(x_562, 0);
lean_inc_ref(x_606);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_607 = x_562;
} else {
 lean_dec_ref(x_562);
 x_607 = lean_box(0);
}
x_608 = lean_ctor_get(x_606, 15);
lean_inc_ref(x_608);
lean_dec_ref(x_606);
x_609 = lean_ctor_get(x_564, 0);
lean_inc(x_609);
lean_dec(x_564);
x_610 = lean_ctor_get(x_608, 0);
lean_inc(x_610);
lean_dec_ref(x_608);
x_611 = lean_nat_dec_lt(x_609, x_610);
lean_dec(x_610);
lean_dec(x_609);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; uint8_t x_614; 
lean_dec(x_607);
lean_dec(x_560);
x_612 = lean_mk_empty_array_with_capacity(x_558);
lean_dec(x_558);
x_613 = lean_array_get_size(x_559);
x_614 = lean_nat_dec_lt(x_545, x_613);
if (x_614 == 0)
{
lean_dec_ref(x_559);
x_599 = x_612;
goto block_605;
}
else
{
uint8_t x_615; 
x_615 = lean_nat_dec_le(x_613, x_613);
if (x_615 == 0)
{
if (x_614 == 0)
{
lean_dec_ref(x_559);
x_599 = x_612;
goto block_605;
}
else
{
size_t x_616; size_t x_617; lean_object* x_618; 
x_616 = 0;
x_617 = lean_usize_of_nat(x_613);
x_618 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_559, x_616, x_617, x_612);
lean_dec_ref(x_559);
x_599 = x_618;
goto block_605;
}
}
else
{
size_t x_619; size_t x_620; lean_object* x_621; 
x_619 = 0;
x_620 = lean_usize_of_nat(x_613);
x_621 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(x_559, x_619, x_620, x_612);
lean_dec_ref(x_559);
x_599 = x_621;
goto block_605;
}
}
}
else
{
lean_object* x_622; 
lean_dec_ref(x_559);
lean_dec(x_558);
lean_dec(x_2);
x_622 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; uint8_t x_625; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 x_624 = x_622;
} else {
 lean_dec_ref(x_622);
 x_624 = lean_box(0);
}
x_625 = lean_ctor_get_uint8(x_623, sizeof(void*)*10 + 14);
lean_dec(x_623);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
lean_dec(x_607);
lean_dec(x_560);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_626 = lean_box(x_561);
if (lean_is_scalar(x_624)) {
 x_627 = lean_alloc_ctor(0, 1, 0);
} else {
 x_627 = x_624;
}
lean_ctor_set(x_627, 0, x_626);
return x_627;
}
else
{
lean_object* x_628; 
lean_dec(x_624);
x_628 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
lean_dec_ref(x_628);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec(x_629);
x_631 = l_Lean_Meta_Grind_mbtc___closed__8;
x_632 = l_Nat_reprFast(x_630);
x_633 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_633, 0, x_632);
x_634 = l_Lean_MessageData_ofFormat(x_633);
if (lean_is_scalar(x_607)) {
 x_635 = lean_alloc_ctor(7, 2, 0);
} else {
 x_635 = x_607;
 lean_ctor_set_tag(x_635, 7);
}
lean_ctor_set(x_635, 0, x_631);
lean_ctor_set(x_635, 1, x_634);
x_636 = l_Lean_Meta_Grind_mbtc___closed__10;
if (lean_is_scalar(x_560)) {
 x_637 = lean_alloc_ctor(7, 2, 0);
} else {
 x_637 = x_560;
 lean_ctor_set_tag(x_637, 7);
}
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
x_638 = l_Lean_Meta_Grind_reportIssue(x_637, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_639 = x_638;
} else {
 lean_dec_ref(x_638);
 x_639 = lean_box(0);
}
x_640 = lean_box(x_561);
if (lean_is_scalar(x_639)) {
 x_641 = lean_alloc_ctor(0, 1, 0);
} else {
 x_641 = x_639;
}
lean_ctor_set(x_641, 0, x_640);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_638, 0);
lean_inc(x_642);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_643 = x_638;
} else {
 lean_dec_ref(x_638);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 1, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_642);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_607);
lean_dec(x_560);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_645 = lean_ctor_get(x_628, 0);
lean_inc(x_645);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 x_646 = x_628;
} else {
 lean_dec_ref(x_628);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 1, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_645);
return x_647;
}
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_607);
lean_dec(x_560);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_648 = lean_ctor_get(x_622, 0);
lean_inc(x_648);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 x_649 = x_622;
} else {
 lean_dec_ref(x_622);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_648);
return x_650;
}
}
block_586:
{
lean_object* x_566; lean_object* x_567; 
x_566 = lean_array_get_size(x_565);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_567 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_565, x_545, x_566, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_565);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 x_569 = x_567;
} else {
 lean_dec_ref(x_567);
 x_569 = lean_box(0);
}
x_570 = l_Array_isEmpty___redArg(x_568);
if (x_570 == 0)
{
lean_object* x_571; size_t x_572; size_t x_573; lean_object* x_574; 
lean_dec(x_569);
x_571 = lean_box(0);
x_572 = lean_array_size(x_568);
x_573 = 0;
x_574 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(x_571, x_568, x_572, x_573, x_571, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_568);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 x_575 = x_574;
} else {
 lean_dec_ref(x_574);
 x_575 = lean_box(0);
}
x_576 = lean_box(x_535);
if (lean_is_scalar(x_575)) {
 x_577 = lean_alloc_ctor(0, 1, 0);
} else {
 x_577 = x_575;
}
lean_ctor_set(x_577, 0, x_576);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_574, 0);
lean_inc(x_578);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 x_579 = x_574;
} else {
 lean_dec_ref(x_574);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 1, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_578);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; 
lean_dec(x_568);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_581 = lean_box(x_561);
if (lean_is_scalar(x_569)) {
 x_582 = lean_alloc_ctor(0, 1, 0);
} else {
 x_582 = x_569;
}
lean_ctor_set(x_582, 0, x_581);
return x_582;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_583 = lean_ctor_get(x_567, 0);
lean_inc(x_583);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 x_584 = x_567;
} else {
 lean_dec_ref(x_567);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 1, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_583);
return x_585;
}
}
block_592:
{
lean_object* x_591; 
lean_dec(x_587);
x_591 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_589, x_588, x_590);
lean_dec(x_590);
x_565 = x_591;
goto block_586;
}
block_598:
{
uint8_t x_597; 
x_597 = lean_nat_dec_le(x_596, x_593);
if (x_597 == 0)
{
lean_dec(x_593);
lean_inc(x_596);
x_587 = x_594;
x_588 = x_596;
x_589 = x_595;
x_590 = x_596;
goto block_592;
}
else
{
x_587 = x_594;
x_588 = x_596;
x_589 = x_595;
x_590 = x_593;
goto block_592;
}
}
block_605:
{
lean_object* x_600; uint8_t x_601; 
x_600 = lean_array_get_size(x_599);
x_601 = lean_nat_dec_eq(x_600, x_545);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_602 = lean_unsigned_to_nat(1u);
x_603 = lean_nat_sub(x_600, x_602);
x_604 = lean_nat_dec_le(x_545, x_603);
if (x_604 == 0)
{
lean_inc(x_603);
x_593 = x_603;
x_594 = x_600;
x_595 = x_599;
x_596 = x_603;
goto block_598;
}
else
{
x_593 = x_603;
x_594 = x_600;
x_595 = x_599;
x_596 = x_545;
goto block_598;
}
}
else
{
x_565 = x_599;
goto block_586;
}
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec(x_558);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_651 = lean_ctor_get(x_563, 0);
lean_inc(x_651);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_652 = x_563;
} else {
 lean_dec_ref(x_563);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 1, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_651);
return x_653;
}
}
else
{
lean_object* x_654; 
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec(x_558);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_556)) {
 x_654 = lean_alloc_ctor(0, 1, 0);
} else {
 x_654 = x_556;
}
lean_ctor_set(x_654, 0, x_539);
return x_654;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_539);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_655 = lean_ctor_get(x_554, 0);
lean_inc(x_655);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 x_656 = x_554;
} else {
 lean_dec_ref(x_554);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 1, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_655);
return x_657;
}
}
else
{
uint8_t x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_539);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_658 = 0;
x_659 = lean_box(x_658);
if (lean_is_scalar(x_540)) {
 x_660 = lean_alloc_ctor(0, 1, 0);
} else {
 x_660 = x_540;
}
lean_ctor_set(x_660, 0, x_659);
return x_660;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_538;
}
}
}
}
else
{
uint8_t x_661; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_661 = !lean_is_exclusive(x_13);
if (x_661 == 0)
{
return x_13;
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_13, 0);
lean_inc(x_662);
lean_dec(x_13);
x_663 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_663, 0, x_662);
return x_663;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_mbtc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
x_22 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_22; 
x_22 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, size_t x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; 
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_31;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args) {
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
_start:
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_32 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_33 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_31, x_32, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; 
x_23 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_23; 
x_23 = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; 
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___boxed(lean_object** _args) {
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
_start:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_24 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5_spec__16___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___closed__2);
l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0 = _init_l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___redArg___closed__5);
l_Lean_Meta_Grind_mbtc___closed__0 = _init_l_Lean_Meta_Grind_mbtc___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mbtc___closed__0);
l_Lean_Meta_Grind_mbtc___closed__1 = _init_l_Lean_Meta_Grind_mbtc___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mbtc___closed__1);
l_Lean_Meta_Grind_mbtc___closed__6 = _init_l_Lean_Meta_Grind_mbtc___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_mbtc___closed__6);
l_Lean_Meta_Grind_mbtc___closed__8 = _init_l_Lean_Meta_Grind_mbtc___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_mbtc___closed__8);
l_Lean_Meta_Grind_mbtc___closed__10 = _init_l_Lean_Meta_Grind_mbtc___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_mbtc___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
