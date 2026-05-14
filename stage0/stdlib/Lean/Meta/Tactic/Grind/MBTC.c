// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MBTC
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.CastLike
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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_SplitInfo_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_isKnownCaseSplit___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "__grind_main_arg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 28, 25, 170, 231, 254, 59, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "__grind_other_arg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 27, 42, 236, 138, 38, 28, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 200, 238, 83, 121, 101, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 58, 101, 243, 41, 236, 253, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__2;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "skipping `mbtc`, maximum number of splits has been reached `(splits := "};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__4;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_expr_eqv(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(v_x_4_, v_x_5_);
lean_dec_ref(v_x_5_);
lean_dec_ref(v_x_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(lean_object* v_x_10_){
_start:
{
uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; 
v___x_11_ = 0ULL;
v___x_12_ = l_Lean_Expr_hash(v_x_10_);
v___x_13_ = lean_uint64_mix_hash(v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(lean_object* v_x_14_){
_start:
{
uint64_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_x_14_);
lean_dec_ref(v_x_14_);
v_r_16_ = lean_box_uint64(v_res_15_);
return v_r_16_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1));
v___x_24_ = l_Lean_mkConst(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2);
return v___x_25_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
v___x_30_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1));
v___x_31_ = l_Lean_mkConst(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(lean_object* v_upperBound_33_, lean_object* v_i_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_b_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_a_44_; uint8_t v___x_48_; 
v___x_48_ = lean_nat_dec_lt(v_a_36_, v_upperBound_33_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec(v_a_36_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v_b_37_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_eq(v_i_34_, v_a_36_);
if (v___x_50_ == 0)
{
lean_object* v_paramInfo_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_paramInfo_51_ = lean_ctor_get(v_a_35_, 0);
v___x_52_ = lean_array_fget_borrowed(v_b_37_, v_a_36_);
lean_inc(v___x_52_);
v___x_53_ = l_Lean_Meta_Sym_Canon_isSupport(v_paramInfo_51_, v_a_36_, v___x_52_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; uint8_t v___x_58_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref(v___x_53_);
v___x_58_ = lean_unbox(v_a_54_);
lean_dec(v_a_54_);
if (v___x_58_ == 0)
{
goto v___jp_55_;
}
else
{
if (v___x_50_ == 0)
{
v_a_44_ = v_b_37_;
goto v___jp_43_;
}
else
{
goto v___jp_55_;
}
}
v___jp_55_:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
v___x_57_ = lean_array_fset(v_b_37_, v_a_36_, v___x_56_);
v_a_44_ = v___x_57_;
goto v___jp_43_;
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
lean_dec_ref(v_b_37_);
lean_dec(v_a_36_);
v_a_59_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_53_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_53_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
v___x_68_ = lean_array_fset(v_b_37_, v_a_36_, v___x_67_);
v_a_44_ = v___x_68_;
goto v___jp_43_;
}
}
v___jp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_a_36_, v___x_45_);
lean_dec(v_a_36_);
v_a_36_ = v___x_46_;
v_b_37_ = v_a_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object* v_upperBound_69_, lean_object* v_i_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_b_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_69_, v_i_70_, v_a_71_, v_a_72_, v_b_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec_ref(v_a_71_);
lean_dec(v_i_70_);
lean_dec(v_upperBound_69_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object* v_i_80_, lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
if (lean_obj_tag(v_x_81_) == 5)
{
lean_object* v_fn_89_; lean_object* v_arg_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_fn_89_ = lean_ctor_get(v_x_81_, 0);
lean_inc_ref(v_fn_89_);
v_arg_90_ = lean_ctor_get(v_x_81_, 1);
lean_inc_ref(v_arg_90_);
lean_dec_ref(v_x_81_);
v___x_91_ = lean_array_set(v_x_82_, v_x_83_, v_arg_90_);
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_sub(v_x_83_, v___x_92_);
lean_dec(v_x_83_);
v_x_81_ = v_fn_89_;
v_x_82_ = v___x_91_;
v_x_83_ = v___x_93_;
goto _start;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_x_83_);
v___x_95_ = lean_box(0);
lean_inc_ref(v_x_81_);
v___x_96_ = l_Lean_Meta_getFunInfo(v_x_81_, v___x_95_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref(v___x_96_);
v___x_98_ = lean_array_get_size(v_x_82_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v___x_98_, v_i_80_, v_a_97_, v___x_99_, v_x_82_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v_a_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = l_Lean_mkAppN(v_x_81_, v_a_101_);
lean_dec(v_a_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_x_81_);
v_a_110_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_x_82_);
lean_dec_ref(v_x_81_);
v_a_118_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_96_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_96_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object* v_i_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_x_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_126_, v_x_127_, v_x_128_, v_x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v_i_126_);
return v_res_135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v_dummy_137_; 
v___x_136_ = lean_box(0);
v_dummy_137_ = l_Lean_Expr_sort___override(v___x_136_);
return v_dummy_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object* v_e_138_, lean_object* v_i_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_dummy_145_; lean_object* v_nargs_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_dummy_145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_146_ = l_Lean_Expr_getAppNumArgs(v_e_138_);
lean_inc(v_nargs_146_);
v___x_147_ = lean_mk_array(v_nargs_146_, v_dummy_145_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_sub(v_nargs_146_, v___x_148_);
lean_dec(v_nargs_146_);
v___x_150_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_139_, v_e_138_, v___x_147_, v___x_149_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object* v_e_151_, lean_object* v_i_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_151_, v_i_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_i_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object* v_upperBound_159_, lean_object* v_i_160_, lean_object* v_a_161_, lean_object* v___x_162_, lean_object* v_inst_163_, lean_object* v_R_164_, lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v_c_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_159_, v_i_160_, v_a_161_, v_a_165_, v_b_166_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object* v_upperBound_174_, lean_object* v_i_175_, lean_object* v_a_176_, lean_object* v___x_177_, lean_object* v_inst_178_, lean_object* v_R_179_, lean_object* v_a_180_, lean_object* v_b_181_, lean_object* v_c_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_174_, v_i_175_, v_a_176_, v___x_177_, v_inst_178_, v_R_179_, v_a_180_, v_b_181_, v_c_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___x_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_i_175_);
lean_dec(v_upperBound_174_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(lean_object* v_a_189_, lean_object* v_b_190_, lean_object* v_i_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_arg_199_; lean_object* v_app_200_; lean_object* v_arg_201_; lean_object* v_app_202_; lean_object* v_fst_204_; lean_object* v_snd_205_; uint8_t v___x_245_; 
v_arg_199_ = lean_ctor_get(v_a_189_, 0);
lean_inc_ref(v_arg_199_);
v_app_200_ = lean_ctor_get(v_a_189_, 1);
lean_inc_ref(v_app_200_);
lean_dec_ref(v_a_189_);
v_arg_201_ = lean_ctor_get(v_b_190_, 0);
lean_inc_ref(v_arg_201_);
v_app_202_ = lean_ctor_get(v_b_190_, 1);
lean_inc_ref(v_app_202_);
lean_dec_ref(v_b_190_);
v___x_245_ = lean_expr_lt(v_arg_199_, v_arg_201_);
if (v___x_245_ == 0)
{
v_fst_204_ = v_arg_201_;
v_snd_205_ = v_arg_199_;
goto v___jp_203_;
}
else
{
v_fst_204_ = v_arg_199_;
v_snd_205_ = v_arg_201_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_mkEq(v_fst_204_, v_snd_205_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_Meta_Sym_canon(v_a_207_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_209_, v_a_193_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_220_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_220_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_inc(v_i_191_);
lean_inc_ref(v_app_202_);
lean_inc_ref(v_app_200_);
v___x_215_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_215_, 0, v_app_200_);
lean_ctor_set(v___x_215_, 1, v_app_202_);
lean_ctor_set(v___x_215_, 2, v_i_191_);
v___x_216_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_216_, 0, v_app_200_);
lean_ctor_set(v___x_216_, 1, v_app_202_);
lean_ctor_set(v___x_216_, 2, v_i_191_);
lean_ctor_set(v___x_216_, 3, v_a_211_);
lean_ctor_set(v___x_216_, 4, v___x_215_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_216_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_app_202_);
lean_dec_ref(v_app_200_);
lean_dec(v_i_191_);
v_a_221_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_210_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_210_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v_app_202_);
lean_dec_ref(v_app_200_);
lean_dec(v_i_191_);
v_a_229_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_208_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_208_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v_app_202_);
lean_dec_ref(v_app_200_);
lean_dec(v_i_191_);
v_a_237_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_206_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_206_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg___boxed(lean_object* v_a_246_, lean_object* v_b_247_, lean_object* v_i_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_246_, v_b_247_, v_i_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object* v_a_257_, lean_object* v_b_258_, lean_object* v_i_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_257_, v_b_258_, v_i_259_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object* v_a_272_, lean_object* v_b_273_, lean_object* v_i_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(v_a_272_, v_b_273_, v_i_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object* v_declName_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v_env_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_290_ = lean_st_ref_get(v___y_288_);
v_env_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_env_291_);
lean_dec(v___x_290_);
v___x_292_ = l_Lean_isImplicitReducibleCore(v_env_291_, v_declName_287_);
v___x_293_ = lean_box(v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object* v_declName_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_295_, v___y_296_);
lean_dec(v___y_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object* v_declName_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_299_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object* v_declName_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object* v_f_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
if (lean_obj_tag(v_f_309_) == 4)
{
lean_object* v_declName_313_; lean_object* v___x_314_; 
v_declName_313_ = lean_ctor_get(v_f_309_, 0);
lean_inc(v_declName_313_);
lean_dec_ref(v_f_309_);
v___x_314_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_313_, v_a_311_);
return v___x_314_;
}
else
{
uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec_ref(v_f_309_);
v___x_315_ = 0;
v___x_316_ = lean_box(v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object* v_f_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v_f_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* v_as_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_b_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_b_326_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_array_uget_borrowed(v_as_323_, v_i_325_);
lean_inc(v_a_340_);
v___x_341_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_340_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; 
lean_dec_ref(v___x_341_);
v___x_342_ = lean_box(0);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_325_, v___x_343_);
v_i_325_ = v___x_344_;
v_b_326_ = v___x_342_;
goto _start;
}
else
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* v_as_346_, lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
size_t v_sz_boxed_361_; size_t v_i_boxed_362_; lean_object* v_res_363_; 
v_sz_boxed_361_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_362_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_346_, v_sz_boxed_361_, v_i_boxed_362_, v_b_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v_as_346_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
return v_x_364_;
}
else
{
lean_object* v_key_366_; lean_object* v_tail_367_; lean_object* v___x_368_; 
v_key_366_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_key_366_);
v_tail_367_ = lean_ctor_get(v_x_365_, 2);
lean_inc(v_tail_367_);
lean_dec_ref(v_x_365_);
v___x_368_ = lean_array_push(v_x_364_, v_key_366_);
v_x_364_ = v___x_368_;
v_x_365_ = v_tail_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object* v_as_370_, size_t v_i_371_, size_t v_stop_372_, lean_object* v_b_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = lean_usize_dec_eq(v_i_371_, v_stop_372_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; 
v___x_375_ = lean_array_uget_borrowed(v_as_370_, v_i_371_);
lean_inc(v___x_375_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(v_b_373_, v___x_375_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_371_, v___x_377_);
v_i_371_ = v___x_378_;
v_b_373_ = v___x_376_;
goto _start;
}
else
{
return v_b_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object* v_as_380_, lean_object* v_i_381_, lean_object* v_stop_382_, lean_object* v_b_383_){
_start:
{
size_t v_i_boxed_384_; size_t v_stop_boxed_385_; lean_object* v_res_386_; 
v_i_boxed_384_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_stop_boxed_385_ = lean_unbox_usize(v_stop_382_);
lean_dec(v_stop_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_380_, v_i_boxed_384_, v_stop_boxed_385_, v_b_383_);
lean_dec_ref(v_as_380_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(lean_object* v_hi_387_, lean_object* v_pivot_388_, lean_object* v_as_389_, lean_object* v_i_390_, lean_object* v_k_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_lt(v_k_391_, v_hi_387_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_k_391_);
v___x_393_ = lean_array_fswap(v_as_389_, v_i_390_, v_hi_387_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_i_390_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_fget_borrowed(v_as_389_, v_k_391_);
v___x_396_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_395_, v_pivot_388_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_k_391_, v___x_397_);
lean_dec(v_k_391_);
v_k_391_ = v___x_398_;
goto _start;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = lean_array_fswap(v_as_389_, v_i_390_, v_k_391_);
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_nat_add(v_i_390_, v___x_401_);
lean_dec(v_i_390_);
v___x_403_ = lean_nat_add(v_k_391_, v___x_401_);
lean_dec(v_k_391_);
v_as_389_ = v___x_400_;
v_i_390_ = v___x_402_;
v_k_391_ = v___x_403_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg___boxed(lean_object* v_hi_405_, lean_object* v_pivot_406_, lean_object* v_as_407_, lean_object* v_i_408_, lean_object* v_k_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_405_, v_pivot_406_, v_as_407_, v_i_408_, v_k_409_);
lean_dec_ref(v_pivot_406_);
lean_dec(v_hi_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object* v_n_411_, lean_object* v_as_412_, lean_object* v_lo_413_, lean_object* v_hi_414_){
_start:
{
lean_object* v___y_416_; uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_lt(v_lo_413_, v_hi_414_);
if (v___x_426_ == 0)
{
lean_dec(v_lo_413_);
return v_as_412_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_mid_429_; lean_object* v___y_431_; lean_object* v___y_437_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_427_ = lean_nat_add(v_lo_413_, v_hi_414_);
v___x_428_ = lean_unsigned_to_nat(1u);
v_mid_429_ = lean_nat_shiftr(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
v___x_442_ = lean_array_fget_borrowed(v_as_412_, v_mid_429_);
v___x_443_ = lean_array_fget_borrowed(v_as_412_, v_lo_413_);
v___x_444_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
v___y_437_ = v_as_412_;
goto v___jp_436_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_array_fswap(v_as_412_, v_lo_413_, v_mid_429_);
v___y_437_ = v___x_445_;
goto v___jp_436_;
}
v___jp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_array_fget_borrowed(v___y_431_, v_mid_429_);
v___x_433_ = lean_array_fget_borrowed(v___y_431_, v_hi_414_);
v___x_434_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v_mid_429_);
v___y_416_ = v___y_431_;
goto v___jp_415_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = lean_array_fswap(v___y_431_, v_mid_429_, v_hi_414_);
lean_dec(v_mid_429_);
v___y_416_ = v___x_435_;
goto v___jp_415_;
}
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_array_fget_borrowed(v___y_437_, v_hi_414_);
v___x_439_ = lean_array_fget_borrowed(v___y_437_, v_lo_413_);
v___x_440_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
v___y_431_ = v___y_437_;
goto v___jp_430_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_array_fswap(v___y_437_, v_lo_413_, v_hi_414_);
v___y_431_ = v___x_441_;
goto v___jp_430_;
}
}
}
v___jp_415_:
{
lean_object* v_pivot_417_; lean_object* v___x_418_; lean_object* v_fst_419_; lean_object* v_snd_420_; uint8_t v___x_421_; 
v_pivot_417_ = lean_array_fget(v___y_416_, v_hi_414_);
lean_inc_n(v_lo_413_, 2);
v___x_418_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_414_, v_pivot_417_, v___y_416_, v_lo_413_, v_lo_413_);
lean_dec(v_pivot_417_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_fst_419_);
v_snd_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v___x_418_);
v___x_421_ = lean_nat_dec_le(v_hi_414_, v_fst_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_411_, v_snd_420_, v_lo_413_, v_fst_419_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_fst_419_, v___x_423_);
lean_dec(v_fst_419_);
v_as_412_ = v___x_422_;
v_lo_413_ = v___x_424_;
goto _start;
}
else
{
lean_dec(v_fst_419_);
lean_dec(v_lo_413_);
return v_snd_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object* v_n_446_, lean_object* v_as_447_, lean_object* v_lo_448_, lean_object* v_hi_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_446_, v_as_447_, v_lo_448_, v_hi_449_);
lean_dec(v_hi_449_);
lean_dec(v_n_446_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_key_454_; lean_object* v_value_455_; lean_object* v_tail_456_; uint8_t v___x_457_; 
v_key_454_ = lean_ctor_get(v_x_452_, 0);
v_value_455_ = lean_ctor_get(v_x_452_, 1);
v_tail_456_ = lean_ctor_get(v_x_452_, 2);
v___x_457_ = lean_expr_eqv(v_key_454_, v_a_451_);
if (v___x_457_ == 0)
{
v_x_452_ = v_tail_456_;
goto _start;
}
else
{
lean_object* v___x_459_; 
lean_inc(v_value_455_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_value_455_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec_ref(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* v_m_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_buckets_465_; lean_object* v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v_fold_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_buckets_465_ = lean_ctor_get(v_m_463_, 1);
v___x_466_ = lean_array_get_size(v_buckets_465_);
v___x_467_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_464_);
v___x_468_ = 32ULL;
v___x_469_ = lean_uint64_shift_right(v___x_467_, v___x_468_);
v_fold_470_ = lean_uint64_xor(v___x_467_, v___x_469_);
v___x_471_ = 16ULL;
v___x_472_ = lean_uint64_shift_right(v_fold_470_, v___x_471_);
v___x_473_ = lean_uint64_xor(v_fold_470_, v___x_472_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = lean_usize_of_nat(v___x_466_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_usize_land(v___x_474_, v___x_477_);
v___x_479_ = lean_array_uget_borrowed(v_buckets_465_, v___x_478_);
v___x_480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_464_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_481_, v_a_482_);
lean_dec_ref(v_a_482_);
lean_dec_ref(v_m_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_lctx_494_; lean_object* v_options_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_490_);
v___x_492_ = lean_st_ref_get(v___y_486_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_mctx_493_);
lean_dec(v___x_492_);
v_lctx_494_ = lean_ctor_get(v___y_485_, 2);
v_options_495_ = lean_ctor_get(v___y_487_, 2);
lean_inc_ref(v_options_495_);
lean_inc_ref(v_lctx_494_);
v___x_496_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_496_, 0, v_env_491_);
lean_ctor_set(v___x_496_, 1, v_mctx_493_);
lean_ctor_set(v___x_496_, 2, v_lctx_494_);
lean_ctor_set(v___x_496_, 3, v_options_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_msgData_484_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object* v_msgData_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_506_; double v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_float_of_nat(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* v_cls_511_, lean_object* v_msg_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_ref_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_565_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 5);
v___x_519_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_565_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_565_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_565_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v_traceState_525_; lean_object* v_env_526_; lean_object* v_nextMacroScope_527_; lean_object* v_ngen_528_; lean_object* v_auxDeclNGen_529_; lean_object* v_cache_530_; lean_object* v_messages_531_; lean_object* v_infoState_532_; lean_object* v_snapshotTasks_533_; lean_object* v_newDecls_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_564_; 
v___x_524_ = lean_st_ref_take(v___y_516_);
v_traceState_525_ = lean_ctor_get(v___x_524_, 4);
v_env_526_ = lean_ctor_get(v___x_524_, 0);
v_nextMacroScope_527_ = lean_ctor_get(v___x_524_, 1);
v_ngen_528_ = lean_ctor_get(v___x_524_, 2);
v_auxDeclNGen_529_ = lean_ctor_get(v___x_524_, 3);
v_cache_530_ = lean_ctor_get(v___x_524_, 5);
v_messages_531_ = lean_ctor_get(v___x_524_, 6);
v_infoState_532_ = lean_ctor_get(v___x_524_, 7);
v_snapshotTasks_533_ = lean_ctor_get(v___x_524_, 8);
v_newDecls_534_ = lean_ctor_get(v___x_524_, 9);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_564_ == 0)
{
v___x_536_ = v___x_524_;
v_isShared_537_ = v_isSharedCheck_564_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_newDecls_534_);
lean_inc(v_snapshotTasks_533_);
lean_inc(v_infoState_532_);
lean_inc(v_messages_531_);
lean_inc(v_cache_530_);
lean_inc(v_traceState_525_);
lean_inc(v_auxDeclNGen_529_);
lean_inc(v_ngen_528_);
lean_inc(v_nextMacroScope_527_);
lean_inc(v_env_526_);
lean_dec(v___x_524_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_564_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint64_t v_tid_538_; lean_object* v_traces_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_563_; 
v_tid_538_ = lean_ctor_get_uint64(v_traceState_525_, sizeof(void*)*1);
v_traces_539_ = lean_ctor_get(v_traceState_525_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_traceState_525_);
if (v_isSharedCheck_563_ == 0)
{
v___x_541_ = v_traceState_525_;
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_traces_539_);
lean_dec(v_traceState_525_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; double v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_545_ = 0;
v___x_546_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_547_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_547_, 0, v_cls_511_);
lean_ctor_set(v___x_547_, 1, v___x_543_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
lean_ctor_set_float(v___x_547_, sizeof(void*)*3, v___x_544_);
lean_ctor_set_float(v___x_547_, sizeof(void*)*3 + 8, v___x_544_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*3 + 16, v___x_545_);
v___x_548_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_549_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v_a_520_);
lean_ctor_set(v___x_549_, 2, v___x_548_);
lean_inc(v_ref_518_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_ref_518_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_Lean_PersistentArray_push___redArg(v_traces_539_, v___x_550_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_551_);
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_551_);
lean_ctor_set_uint64(v_reuseFailAlloc_562_, sizeof(void*)*1, v_tid_538_);
v___x_553_ = v_reuseFailAlloc_562_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___x_553_);
v___x_555_ = v___x_536_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_env_526_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_527_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_528_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_cache_530_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_messages_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_infoState_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_snapshotTasks_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_newDecls_534_);
v___x_555_ = v_reuseFailAlloc_561_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_st_ref_set(v___y_516_, v___x_555_);
v___x_557_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_557_);
v___x_559_ = v___x_522_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_566_, v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
uint8_t v___x_576_; 
v___x_576_ = 0;
return v___x_576_;
}
else
{
lean_object* v_key_577_; lean_object* v_tail_578_; uint8_t v___x_579_; 
v_key_577_ = lean_ctor_get(v_x_575_, 0);
v_tail_578_ = lean_ctor_get(v_x_575_, 2);
v___x_579_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_577_, v_a_574_);
if (v___x_579_ == 0)
{
v_x_575_ = v_tail_578_;
goto _start;
}
else
{
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec_ref(v_a_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
return v_x_585_;
}
else
{
lean_object* v_key_587_; lean_object* v_value_588_; lean_object* v_tail_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_612_; 
v_key_587_ = lean_ctor_get(v_x_586_, 0);
v_value_588_ = lean_ctor_get(v_x_586_, 1);
v_tail_589_ = lean_ctor_get(v_x_586_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_612_ == 0)
{
v___x_591_ = v_x_586_;
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_tail_589_);
lean_inc(v_value_588_);
lean_inc(v_key_587_);
lean_dec(v_x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v_fold_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_593_ = lean_array_get_size(v_x_585_);
v___x_594_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_587_);
v___x_595_ = 32ULL;
v___x_596_ = lean_uint64_shift_right(v___x_594_, v___x_595_);
v_fold_597_ = lean_uint64_xor(v___x_594_, v___x_596_);
v___x_598_ = 16ULL;
v___x_599_ = lean_uint64_shift_right(v_fold_597_, v___x_598_);
v___x_600_ = lean_uint64_xor(v_fold_597_, v___x_599_);
v___x_601_ = lean_uint64_to_usize(v___x_600_);
v___x_602_ = lean_usize_of_nat(v___x_593_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_sub(v___x_602_, v___x_603_);
v___x_605_ = lean_usize_land(v___x_601_, v___x_604_);
v___x_606_ = lean_array_uget_borrowed(v_x_585_, v___x_605_);
lean_inc(v___x_606_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 2, v___x_606_);
v___x_608_ = v___x_591_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_key_587_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_value_588_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v___x_606_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_array_uset(v_x_585_, v___x_605_, v___x_608_);
v_x_585_ = v___x_609_;
v_x_586_ = v_tail_589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object* v_i_613_, lean_object* v_source_614_, lean_object* v_target_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_source_614_);
v___x_617_ = lean_nat_dec_lt(v_i_613_, v___x_616_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_source_614_);
lean_dec(v_i_613_);
return v_target_615_;
}
else
{
lean_object* v_es_618_; lean_object* v___x_619_; lean_object* v_source_620_; lean_object* v_target_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_es_618_ = lean_array_fget(v_source_614_, v_i_613_);
v___x_619_ = lean_box(0);
v_source_620_ = lean_array_fset(v_source_614_, v_i_613_, v___x_619_);
v_target_621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_615_, v_es_618_);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v_i_613_, v___x_622_);
lean_dec(v_i_613_);
v_i_613_ = v___x_623_;
v_source_614_ = v_source_620_;
v_target_615_ = v_target_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object* v_data_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_nbuckets_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_626_ = lean_array_get_size(v_data_625_);
v___x_627_ = lean_unsigned_to_nat(2u);
v_nbuckets_628_ = lean_nat_mul(v___x_626_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_box(0);
v___x_631_ = lean_mk_array(v_nbuckets_628_, v___x_630_);
v___x_632_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_629_, v_data_625_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_633_, lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
lean_object* v_size_636_; lean_object* v_buckets_637_; lean_object* v___x_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v_fold_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v_bkt_651_; uint8_t v___x_652_; 
v_size_636_ = lean_ctor_get(v_m_633_, 0);
v_buckets_637_ = lean_ctor_get(v_m_633_, 1);
v___x_638_ = lean_array_get_size(v_buckets_637_);
v___x_639_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_634_);
v___x_640_ = 32ULL;
v___x_641_ = lean_uint64_shift_right(v___x_639_, v___x_640_);
v_fold_642_ = lean_uint64_xor(v___x_639_, v___x_641_);
v___x_643_ = 16ULL;
v___x_644_ = lean_uint64_shift_right(v_fold_642_, v___x_643_);
v___x_645_ = lean_uint64_xor(v_fold_642_, v___x_644_);
v___x_646_ = lean_uint64_to_usize(v___x_645_);
v___x_647_ = lean_usize_of_nat(v___x_638_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v___x_647_, v___x_648_);
v___x_650_ = lean_usize_land(v___x_646_, v___x_649_);
v_bkt_651_ = lean_array_uget_borrowed(v_buckets_637_, v___x_650_);
v___x_652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_634_, v_bkt_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
lean_inc_ref(v_buckets_637_);
lean_inc(v_size_636_);
v_isSharedCheck_673_ = !lean_is_exclusive(v_m_633_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_674_ = lean_ctor_get(v_m_633_, 1);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_m_633_, 0);
lean_dec(v_unused_675_);
v___x_654_ = v_m_633_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_m_633_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v_size_x27_657_; lean_object* v___x_658_; lean_object* v_buckets_x27_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v_size_x27_657_ = lean_nat_add(v_size_636_, v___x_656_);
lean_dec(v_size_636_);
lean_inc(v_bkt_651_);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v_a_634_);
lean_ctor_set(v___x_658_, 1, v_b_635_);
lean_ctor_set(v___x_658_, 2, v_bkt_651_);
v_buckets_x27_659_ = lean_array_uset(v_buckets_637_, v___x_650_, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(4u);
v___x_661_ = lean_nat_mul(v_size_x27_657_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_div(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_array_get_size(v_buckets_x27_659_);
v___x_665_ = lean_nat_dec_le(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
if (v___x_665_ == 0)
{
lean_object* v_val_666_; lean_object* v___x_668_; 
v_val_666_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_659_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_val_666_);
lean_ctor_set(v___x_654_, 0, v_size_x27_657_);
v___x_668_ = v___x_654_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_size_x27_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_val_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_671_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_buckets_x27_659_);
lean_ctor_set(v___x_654_, 0, v_size_x27_657_);
v___x_671_ = v___x_654_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_x27_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_buckets_x27_659_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_dec(v_b_635_);
lean_dec_ref(v_a_634_);
return v_m_633_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_ctx_676_, lean_object* v_val_677_, lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v_as_x27_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
if (lean_obj_tag(v_as_x27_680_) == 0)
{
lean_object* v___x_693_; 
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v_val_677_);
lean_dec_ref(v_ctx_676_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_681_);
return v___x_693_;
}
else
{
lean_object* v_head_694_; lean_object* v_tail_695_; lean_object* v_eqAssignment_696_; lean_object* v_arg_697_; lean_object* v___x_698_; 
v_head_694_ = lean_ctor_get(v_as_x27_680_, 0);
v_tail_695_ = lean_ctor_get(v_as_x27_680_, 1);
v_eqAssignment_696_ = lean_ctor_get(v_ctx_676_, 2);
v_arg_697_ = lean_ctor_get(v_head_694_, 0);
lean_inc_ref(v_eqAssignment_696_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc(v___y_682_);
lean_inc_ref(v_arg_697_);
lean_inc_ref(v_val_677_);
v___x_698_ = lean_apply_13(v_eqAssignment_696_, v_val_677_, v_arg_697_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, lean_box(0));
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; uint8_t v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_unbox(v_a_699_);
lean_dec(v_a_699_);
if (v___x_700_ == 0)
{
v_as_x27_680_ = v_tail_695_;
goto _start;
}
else
{
lean_object* v___x_702_; 
lean_inc_ref(v_arg_697_);
lean_inc_ref(v_val_677_);
v___x_702_ = l_Lean_Meta_Grind_hasSameType(v_val_677_, v_arg_697_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; uint8_t v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_704_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
if (v___x_704_ == 0)
{
v_as_x27_680_ = v_tail_695_;
goto _start;
}
else
{
lean_object* v___x_706_; 
lean_inc(v___x_679_);
lean_inc(v_head_694_);
lean_inc_ref(v___x_678_);
v___x_706_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_678_, v_head_694_, v___x_679_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v___x_708_ = lean_box(0);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_681_, v_a_707_, v___x_708_);
v_as_x27_680_ = v_tail_695_;
v_b_681_ = v___x_709_;
goto _start;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_b_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v_val_677_);
lean_dec_ref(v_ctx_676_);
v_a_711_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_706_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_706_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v_b_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v_val_677_);
lean_dec_ref(v_ctx_676_);
v_a_719_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_702_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_702_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_b_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v_val_677_);
lean_dec_ref(v_ctx_676_);
v_a_727_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_698_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_698_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_ctx_735_ = _args[0];
lean_object* v_val_736_ = _args[1];
lean_object* v___x_737_ = _args[2];
lean_object* v___x_738_ = _args[3];
lean_object* v_as_x27_739_ = _args[4];
lean_object* v_b_740_ = _args[5];
lean_object* v___y_741_ = _args[6];
lean_object* v___y_742_ = _args[7];
lean_object* v___y_743_ = _args[8];
lean_object* v___y_744_ = _args[9];
lean_object* v___y_745_ = _args[10];
lean_object* v___y_746_ = _args[11];
lean_object* v___y_747_ = _args[12];
lean_object* v___y_748_ = _args[13];
lean_object* v___y_749_ = _args[14];
lean_object* v___y_750_ = _args[15];
lean_object* v___y_751_ = _args[16];
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_735_, v_val_736_, v___x_737_, v___x_738_, v_as_x27_739_, v_b_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v_as_x27_739_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* v_a_753_, lean_object* v_b_754_, lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_dec(v_b_754_);
lean_dec_ref(v_a_753_);
return v_x_755_;
}
else
{
lean_object* v_key_756_; lean_object* v_value_757_; lean_object* v_tail_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_key_756_ = lean_ctor_get(v_x_755_, 0);
v_value_757_ = lean_ctor_get(v_x_755_, 1);
v_tail_758_ = lean_ctor_get(v_x_755_, 2);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_755_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v_x_755_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_tail_758_);
lean_inc(v_value_757_);
lean_inc(v_key_756_);
lean_dec(v_x_755_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = lean_expr_eqv(v_key_756_, v_a_753_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_753_, v_b_754_, v_tail_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_763_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_key_756_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_value_757_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_768_; 
lean_dec(v_value_757_);
lean_dec(v_key_756_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_b_754_);
lean_ctor_set(v___x_760_, 0, v_a_753_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_b_754_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_tail_758_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* v_a_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
uint8_t v___x_773_; 
v___x_773_ = 0;
return v___x_773_;
}
else
{
lean_object* v_key_774_; lean_object* v_tail_775_; uint8_t v___x_776_; 
v_key_774_ = lean_ctor_get(v_x_772_, 0);
v_tail_775_ = lean_ctor_get(v_x_772_, 2);
v___x_776_ = lean_expr_eqv(v_key_774_, v_a_771_);
if (v___x_776_ == 0)
{
v_x_772_ = v_tail_775_;
goto _start;
}
else
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* v_a_778_, lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_778_, v_x_779_);
lean_dec(v_x_779_);
lean_dec_ref(v_a_778_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
return v_x_782_;
}
else
{
lean_object* v_key_784_; lean_object* v_value_785_; lean_object* v_tail_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_809_; 
v_key_784_ = lean_ctor_get(v_x_783_, 0);
v_value_785_ = lean_ctor_get(v_x_783_, 1);
v_tail_786_ = lean_ctor_get(v_x_783_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_809_ == 0)
{
v___x_788_ = v_x_783_;
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_tail_786_);
lean_inc(v_value_785_);
lean_inc(v_key_784_);
lean_dec(v_x_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v_fold_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_790_ = lean_array_get_size(v_x_782_);
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_784_);
v___x_792_ = 32ULL;
v___x_793_ = lean_uint64_shift_right(v___x_791_, v___x_792_);
v_fold_794_ = lean_uint64_xor(v___x_791_, v___x_793_);
v___x_795_ = 16ULL;
v___x_796_ = lean_uint64_shift_right(v_fold_794_, v___x_795_);
v___x_797_ = lean_uint64_xor(v_fold_794_, v___x_796_);
v___x_798_ = lean_uint64_to_usize(v___x_797_);
v___x_799_ = lean_usize_of_nat(v___x_790_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_sub(v___x_799_, v___x_800_);
v___x_802_ = lean_usize_land(v___x_798_, v___x_801_);
v___x_803_ = lean_array_uget_borrowed(v_x_782_, v___x_802_);
lean_inc(v___x_803_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___x_803_);
v___x_805_ = v___x_788_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_key_784_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_value_785_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v___x_803_);
v___x_805_ = v_reuseFailAlloc_808_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_array_uset(v_x_782_, v___x_802_, v___x_805_);
v_x_782_ = v___x_806_;
v_x_783_ = v_tail_786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* v_i_810_, lean_object* v_source_811_, lean_object* v_target_812_){
_start:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_array_get_size(v_source_811_);
v___x_814_ = lean_nat_dec_lt(v_i_810_, v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v_source_811_);
lean_dec(v_i_810_);
return v_target_812_;
}
else
{
lean_object* v_es_815_; lean_object* v___x_816_; lean_object* v_source_817_; lean_object* v_target_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_es_815_ = lean_array_fget(v_source_811_, v_i_810_);
v___x_816_ = lean_box(0);
v_source_817_ = lean_array_fset(v_source_811_, v_i_810_, v___x_816_);
v_target_818_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_812_, v_es_815_);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_i_810_, v___x_819_);
lean_dec(v_i_810_);
v_i_810_ = v___x_820_;
v_source_811_ = v_source_817_;
v_target_812_ = v_target_818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* v_data_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_nbuckets_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_823_ = lean_array_get_size(v_data_822_);
v___x_824_ = lean_unsigned_to_nat(2u);
v_nbuckets_825_ = lean_nat_mul(v___x_823_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_box(0);
v___x_828_ = lean_mk_array(v_nbuckets_825_, v___x_827_);
v___x_829_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_826_, v_data_822_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_size_833_; lean_object* v_buckets_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_877_; 
v_size_833_ = lean_ctor_get(v_m_830_, 0);
v_buckets_834_ = lean_ctor_get(v_m_830_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_m_830_);
if (v_isSharedCheck_877_ == 0)
{
v___x_836_ = v_m_830_;
v_isShared_837_ = v_isSharedCheck_877_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_buckets_834_);
lean_inc(v_size_833_);
lean_dec(v_m_830_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_877_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; uint64_t v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v_fold_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v_bkt_851_; uint8_t v___x_852_; 
v___x_838_ = lean_array_get_size(v_buckets_834_);
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_831_);
v___x_840_ = 32ULL;
v___x_841_ = lean_uint64_shift_right(v___x_839_, v___x_840_);
v_fold_842_ = lean_uint64_xor(v___x_839_, v___x_841_);
v___x_843_ = 16ULL;
v___x_844_ = lean_uint64_shift_right(v_fold_842_, v___x_843_);
v___x_845_ = lean_uint64_xor(v_fold_842_, v___x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = lean_usize_of_nat(v___x_838_);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_sub(v___x_847_, v___x_848_);
v___x_850_ = lean_usize_land(v___x_846_, v___x_849_);
v_bkt_851_ = lean_array_uget_borrowed(v_buckets_834_, v___x_850_);
v___x_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_831_, v_bkt_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v_size_x27_854_; lean_object* v___x_855_; lean_object* v_buckets_x27_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v_size_x27_854_ = lean_nat_add(v_size_833_, v___x_853_);
lean_dec(v_size_833_);
lean_inc(v_bkt_851_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v_a_831_);
lean_ctor_set(v___x_855_, 1, v_b_832_);
lean_ctor_set(v___x_855_, 2, v_bkt_851_);
v_buckets_x27_856_ = lean_array_uset(v_buckets_834_, v___x_850_, v___x_855_);
v___x_857_ = lean_unsigned_to_nat(4u);
v___x_858_ = lean_nat_mul(v_size_x27_854_, v___x_857_);
v___x_859_ = lean_unsigned_to_nat(3u);
v___x_860_ = lean_nat_div(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_array_get_size(v_buckets_x27_856_);
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_861_);
lean_dec(v___x_860_);
if (v___x_862_ == 0)
{
lean_object* v_val_863_; lean_object* v___x_865_; 
v_val_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_856_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_val_863_);
lean_ctor_set(v___x_836_, 0, v_size_x27_854_);
v___x_865_ = v___x_836_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_868_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_buckets_x27_856_);
lean_ctor_set(v___x_836_, 0, v_size_x27_854_);
v___x_868_ = v___x_836_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_buckets_x27_856_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v___x_870_; lean_object* v_buckets_x27_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_bkt_851_);
v___x_870_ = lean_box(0);
v_buckets_x27_871_ = lean_array_uset(v_buckets_834_, v___x_850_, v___x_870_);
v___x_872_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_831_, v_b_832_, v_bkt_851_);
v___x_873_ = lean_array_uset(v_buckets_x27_871_, v___x_850_, v___x_872_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_873_);
v___x_875_ = v___x_836_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_size_833_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_878_, lean_object* v_x_879_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
uint8_t v___x_880_; 
v___x_880_ = 0;
return v___x_880_;
}
else
{
lean_object* v_head_881_; lean_object* v_tail_882_; lean_object* v_arg_883_; uint8_t v___x_884_; 
v_head_881_ = lean_ctor_get(v_x_879_, 0);
v_tail_882_ = lean_ctor_get(v_x_879_, 1);
v_arg_883_ = lean_ctor_get(v_head_881_, 0);
v___x_884_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_878_, v_arg_883_);
if (v___x_884_ == 0)
{
v_x_879_ = v_tail_882_;
goto _start;
}
else
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec_ref(v_val_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_902_ = l_Lean_Name_append(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_909_, lean_object* v_ctx_910_, lean_object* v___x_911_, lean_object* v_as_912_, size_t v_sz_913_, size_t v_i_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_a_928_; uint8_t v___x_932_; 
v___x_932_ = lean_usize_dec_lt(v_i_914_, v_sz_913_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctx_910_);
lean_dec_ref(v_e_909_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_b_915_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v_snd_935_; lean_object* v_fst_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1046_; 
v___x_934_ = lean_st_ref_get(v___y_916_);
v_snd_935_ = lean_ctor_get(v_b_915_, 1);
v_fst_936_ = lean_ctor_get(v_b_915_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_b_915_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_938_ = v_b_915_;
v_isShared_939_ = v_isSharedCheck_1046_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_935_);
lean_inc(v_fst_936_);
lean_dec(v_b_915_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1046_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_1045_; 
v_fst_940_ = lean_ctor_get(v_snd_935_, 0);
v_snd_941_ = lean_ctor_get(v_snd_935_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_snd_935_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_943_ = v_snd_935_;
v_isShared_944_ = v_isSharedCheck_1045_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v_snd_935_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_1045_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_map_946_; lean_object* v_candidates_947_; lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_array_uget_borrowed(v_as_912_, v_i_914_);
v___x_957_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_934_, v_a_956_);
lean_dec(v___x_934_);
if (lean_obj_tag(v___x_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1042_; 
v_val_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_1042_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1042_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v_hasTheoryVar_1002_; lean_object* v___x_1003_; 
v_hasTheoryVar_1002_ = lean_ctor_get(v_ctx_910_, 1);
lean_inc_ref(v_hasTheoryVar_1002_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v___y_916_);
lean_inc(v_val_958_);
v___x_1003_ = lean_apply_12(v_hasTheoryVar_1002_, v_val_958_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; uint8_t v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_unbox(v_a_1004_);
lean_dec(v_a_1004_);
if (v___x_1005_ == 0)
{
lean_del_object(v___x_960_);
lean_dec(v_val_958_);
v_map_946_ = v_fst_936_;
v_candidates_947_ = v_fst_940_;
goto v___jp_945_;
}
else
{
lean_object* v_options_1006_; uint8_t v_hasTrace_1007_; 
v_options_1006_ = lean_ctor_get(v___y_924_, 2);
v_hasTrace_1007_ = lean_ctor_get_uint8(v_options_1006_, sizeof(void*)*1);
if (v_hasTrace_1007_ == 0)
{
lean_del_object(v___x_960_);
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
goto v___jp_962_;
}
else
{
lean_object* v_inheritedTraceOptions_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_inheritedTraceOptions_1008_ = lean_ctor_get(v___y_924_, 13);
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1010_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1008_, v_options_1006_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_del_object(v___x_960_);
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_inc(v_val_958_);
v___x_1012_ = l_Lean_MessageData_ofExpr(v_val_958_);
v___x_1013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_inc_ref(v___x_911_);
v___x_1015_ = l_Lean_MessageData_ofExpr(v___x_911_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc(v_snd_941_);
v___x_1019_ = l_Nat_reprFast(v_snd_941_);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 3);
lean_ctor_set(v___x_960_, 0, v___x_1019_);
v___x_1021_ = v___x_960_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = l_Lean_MessageData_ofFormat(v___x_1021_);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1018_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1009_, v___x_1023_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_dec_ref(v___x_1024_);
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
goto v___jp_962_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_val_958_);
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_del_object(v___x_938_);
lean_dec(v_fst_936_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctx_910_);
lean_dec_ref(v_e_909_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_del_object(v___x_960_);
lean_dec(v_val_958_);
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_del_object(v___x_938_);
lean_dec(v_fst_936_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctx_910_);
lean_dec_ref(v_e_909_);
v_a_1034_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1003_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1003_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
v___jp_962_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref_n(v_e_909_, 2);
lean_inc(v_val_958_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_val_958_);
lean_ctor_set(v___x_973_, 1, v_e_909_);
v___x_974_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_909_, v_snd_941_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_936_, v_a_975_);
if (lean_obj_tag(v___x_976_) == 1)
{
lean_object* v_val_977_; uint8_t v___x_978_; 
v_val_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_val_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_958_, v_val_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_inc(v_snd_941_);
lean_inc_ref(v___x_973_);
lean_inc_ref(v_ctx_910_);
v___x_979_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_910_, v_val_958_, v___x_973_, v_snd_941_, v_val_977_, v_fst_940_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_973_);
lean_ctor_set(v___x_981_, 1, v_val_977_);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_936_, v_a_975_, v___x_981_);
v_map_946_ = v___x_982_;
v_candidates_947_ = v_a_980_;
goto v___jp_945_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_val_977_);
lean_dec(v_a_975_);
lean_dec_ref(v___x_973_);
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_del_object(v___x_938_);
lean_dec(v_fst_936_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctx_910_);
lean_dec_ref(v_e_909_);
v_a_983_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_979_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_dec(v_val_977_);
lean_dec(v_a_975_);
lean_dec_ref(v___x_973_);
lean_dec(v_val_958_);
v_map_946_ = v_fst_936_;
v_candidates_947_ = v_fst_940_;
goto v___jp_945_;
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v___x_976_);
lean_dec(v_val_958_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_973_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_936_, v_a_975_, v___x_992_);
v_map_946_ = v___x_993_;
v_candidates_947_ = v_fst_940_;
goto v___jp_945_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v___x_973_);
lean_dec(v_val_958_);
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_del_object(v___x_938_);
lean_dec(v_fst_936_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctx_910_);
lean_dec_ref(v_e_909_);
v_a_994_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_974_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_974_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___x_957_);
lean_del_object(v___x_943_);
lean_del_object(v___x_938_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_fst_940_);
lean_ctor_set(v___x_1043_, 1, v_snd_941_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_fst_936_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v_a_928_ = v___x_1044_;
goto v___jp_927_;
}
v___jp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_snd_941_, v___x_948_);
lean_dec(v_snd_941_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_949_);
lean_ctor_set(v___x_943_, 0, v_candidates_947_);
v___x_951_ = v___x_943_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_candidates_947_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_951_);
lean_ctor_set(v___x_938_, 0, v_map_946_);
v___x_953_ = v___x_938_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_map_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_928_ = v___x_953_;
goto v___jp_927_;
}
}
}
}
}
}
v___jp_927_:
{
size_t v___x_929_; size_t v___x_930_; 
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_i_914_, v___x_929_);
v_i_914_ = v___x_930_;
v_b_915_ = v_a_928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1047_ = _args[0];
lean_object* v_ctx_1048_ = _args[1];
lean_object* v___x_1049_ = _args[2];
lean_object* v_as_1050_ = _args[3];
lean_object* v_sz_1051_ = _args[4];
lean_object* v_i_1052_ = _args[5];
lean_object* v_b_1053_ = _args[6];
lean_object* v___y_1054_ = _args[7];
lean_object* v___y_1055_ = _args[8];
lean_object* v___y_1056_ = _args[9];
lean_object* v___y_1057_ = _args[10];
lean_object* v___y_1058_ = _args[11];
lean_object* v___y_1059_ = _args[12];
lean_object* v___y_1060_ = _args[13];
lean_object* v___y_1061_ = _args[14];
lean_object* v___y_1062_ = _args[15];
lean_object* v___y_1063_ = _args[16];
lean_object* v___y_1064_ = _args[17];
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1051_);
lean_dec(v_sz_1051_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1047_, v_ctx_1048_, v___x_1049_, v_as_1050_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v_as_1050_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1068_, lean_object* v_as_1069_, size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec_ref(v_ctx_1068_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_b_1072_);
return v___x_1085_;
}
else
{
lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1187_; 
v_snd_1086_ = lean_ctor_get(v_b_1072_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_b_1072_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_b_1072_, 0);
lean_dec(v_unused_1188_);
v___x_1088_ = v_b_1072_;
v_isShared_1089_ = v_isSharedCheck_1187_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_dec(v_b_1072_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1187_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1186_; 
v_fst_1090_ = lean_ctor_get(v_snd_1086_, 0);
v_snd_1091_ = lean_ctor_get(v_snd_1086_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_snd_1086_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1093_ = v_snd_1086_;
v_isShared_1094_ = v_isSharedCheck_1186_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_inc(v_fst_1090_);
lean_dec(v_snd_1086_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1186_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v_a_1097_; lean_object* v_a_1110_; uint8_t v___y_1112_; uint8_t v___x_1184_; 
v___x_1095_ = lean_box(0);
v_a_1110_ = lean_array_uget_borrowed(v_as_1069_, v_i_1071_);
v___x_1184_ = l_Lean_Expr_isApp(v_a_1110_);
if (v___x_1184_ == 0)
{
v___y_1112_ = v___x_1184_;
goto v___jp_1111_;
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_Expr_isEq(v_a_1110_);
if (v___x_1185_ == 0)
{
v___y_1112_ = v___x_1184_;
goto v___jp_1111_;
}
else
{
goto v___jp_1104_;
}
}
v___jp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_a_1097_);
lean_ctor_set(v___x_1093_, 0, v___x_1095_);
v___x_1099_ = v___x_1093_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_a_1097_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
size_t v___x_1100_; size_t v___x_1101_; 
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1071_, v___x_1100_);
v_i_1071_ = v___x_1101_;
v_b_1072_ = v___x_1099_;
goto _start;
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_snd_1091_);
lean_ctor_set(v___x_1088_, 0, v_fst_1090_);
v___x_1106_ = v___x_1088_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1090_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_snd_1091_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v_a_1097_ = v___x_1106_;
goto v___jp_1096_;
}
}
v___jp_1108_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_fst_1090_);
lean_ctor_set(v___x_1109_, 1, v_snd_1091_);
v_a_1097_ = v___x_1109_;
goto v___jp_1096_;
}
v___jp_1111_:
{
if (v___y_1112_ == 0)
{
goto v___jp_1104_;
}
else
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Lean_Expr_isHEq(v_a_1110_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_del_object(v___x_1088_);
lean_inc(v_a_1110_);
v___x_1114_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1110_, v___y_1073_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; uint8_t v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_fst_1090_);
lean_ctor_set(v___x_1117_, 1, v_snd_1091_);
v_a_1097_ = v___x_1117_;
goto v___jp_1096_;
}
else
{
lean_object* v_isInterpreted_1118_; lean_object* v___x_1119_; 
v_isInterpreted_1118_ = lean_ctor_get(v_ctx_1068_, 0);
lean_inc_ref(v_isInterpreted_1118_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc(v_a_1110_);
v___x_1119_ = lean_apply_12(v_isInterpreted_1118_, v_a_1110_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; uint8_t v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = l_Lean_Expr_getAppFn(v_a_1110_);
lean_inc_ref(v___x_1122_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1122_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1122_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v_dummy_1128_; lean_object* v_nargs_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v_dummy_1128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1129_ = l_Lean_Expr_getAppNumArgs(v_a_1110_);
lean_inc(v_nargs_1129_);
v___x_1130_ = lean_mk_array(v_nargs_1129_, v_dummy_1128_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_sub(v_nargs_1129_, v___x_1131_);
lean_dec(v_nargs_1129_);
lean_inc_n(v_a_1110_, 2);
v___x_1133_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1110_, v___x_1130_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_snd_1091_);
lean_ctor_set(v___x_1134_, 1, v___x_1127_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_fst_1090_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v_sz_1136_ = lean_array_size(v___x_1133_);
v___x_1137_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1068_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1110_, v_ctx_1068_, v___x_1122_, v___x_1133_, v_sz_1136_, v___x_1137_, v___x_1135_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec_ref(v___x_1133_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_snd_1140_; lean_object* v_fst_1141_; lean_object* v_fst_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v_snd_1140_ = lean_ctor_get(v_a_1139_, 1);
lean_inc(v_snd_1140_);
v_fst_1141_ = lean_ctor_get(v_a_1139_, 0);
lean_inc(v_fst_1141_);
lean_dec(v_a_1139_);
v_fst_1142_ = lean_ctor_get(v_snd_1140_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_snd_1140_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_snd_1140_, 1);
lean_dec(v_unused_1150_);
v___x_1144_ = v_snd_1140_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_fst_1142_);
lean_dec(v_snd_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_fst_1142_);
lean_ctor_set(v___x_1144_, 0, v_fst_1141_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1141_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_fst_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v_a_1097_ = v___x_1147_;
goto v___jp_1096_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1093_);
lean_dec_ref(v_ctx_1068_);
v_a_1151_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1138_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1138_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_dec_ref(v___x_1122_);
goto v___jp_1108_;
}
}
else
{
lean_dec_ref(v___x_1122_);
goto v___jp_1108_;
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v___x_1122_);
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
lean_dec_ref(v_ctx_1068_);
v_a_1159_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1123_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1123_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_fst_1090_);
lean_ctor_set(v___x_1167_, 1, v_snd_1091_);
v_a_1097_ = v___x_1167_;
goto v___jp_1096_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
lean_dec_ref(v_ctx_1068_);
v_a_1168_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1119_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1119_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
lean_dec_ref(v_ctx_1068_);
v_a_1176_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1114_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1114_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
goto v___jp_1104_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object* v_ctx_1189_, lean_object* v_as_1190_, lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1189_, v_as_1190_, v_sz_boxed_1205_, v_i_boxed_1206_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v_as_1190_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1208_, lean_object* v_as_1209_, size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_usize_dec_lt(v_i_1211_, v_sz_1210_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_ctx_1208_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_b_1212_);
return v___x_1225_;
}
else
{
lean_object* v_snd_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1327_; 
v_snd_1226_ = lean_ctor_get(v_b_1212_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_b_1212_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_b_1212_, 0);
lean_dec(v_unused_1328_);
v___x_1228_ = v_b_1212_;
v_isShared_1229_ = v_isSharedCheck_1327_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snd_1226_);
lean_dec(v_b_1212_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1327_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1326_; 
v_fst_1230_ = lean_ctor_get(v_snd_1226_, 0);
v_snd_1231_ = lean_ctor_get(v_snd_1226_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_snd_1226_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1233_ = v_snd_1226_;
v_isShared_1234_ = v_isSharedCheck_1326_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_inc(v_fst_1230_);
lean_dec(v_snd_1226_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1326_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v_a_1237_; lean_object* v_a_1250_; uint8_t v___y_1252_; uint8_t v___x_1324_; 
v___x_1235_ = lean_box(0);
v_a_1250_ = lean_array_uget_borrowed(v_as_1209_, v_i_1211_);
v___x_1324_ = l_Lean_Expr_isApp(v_a_1250_);
if (v___x_1324_ == 0)
{
v___y_1252_ = v___x_1324_;
goto v___jp_1251_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_Expr_isEq(v_a_1250_);
if (v___x_1325_ == 0)
{
v___y_1252_ = v___x_1324_;
goto v___jp_1251_;
}
else
{
goto v___jp_1244_;
}
}
v___jp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_a_1237_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_a_1237_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((size_t)1ULL);
v___x_1241_ = lean_usize_add(v_i_1211_, v___x_1240_);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1208_, v_as_1209_, v_sz_1210_, v___x_1241_, v___x_1239_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1242_;
}
}
v___jp_1244_:
{
lean_object* v___x_1246_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_snd_1231_);
lean_ctor_set(v___x_1228_, 0, v_fst_1230_);
v___x_1246_ = v___x_1228_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_fst_1230_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_snd_1231_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
v_a_1237_ = v___x_1246_;
goto v___jp_1236_;
}
}
v___jp_1248_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_fst_1230_);
lean_ctor_set(v___x_1249_, 1, v_snd_1231_);
v_a_1237_ = v___x_1249_;
goto v___jp_1236_;
}
v___jp_1251_:
{
if (v___y_1252_ == 0)
{
goto v___jp_1244_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Lean_Expr_isHEq(v_a_1250_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_del_object(v___x_1228_);
lean_inc(v_a_1250_);
v___x_1254_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1250_, v___y_1213_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; uint8_t v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = lean_unbox(v_a_1255_);
lean_dec(v_a_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_fst_1230_);
lean_ctor_set(v___x_1257_, 1, v_snd_1231_);
v_a_1237_ = v___x_1257_;
goto v___jp_1236_;
}
else
{
lean_object* v_isInterpreted_1258_; lean_object* v___x_1259_; 
v_isInterpreted_1258_ = lean_ctor_get(v_ctx_1208_, 0);
lean_inc_ref(v_isInterpreted_1258_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___y_1213_);
lean_inc(v_a_1250_);
v___x_1259_ = lean_apply_12(v_isInterpreted_1258_, v_a_1250_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, lean_box(0));
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; uint8_t v___x_1261_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = lean_unbox(v_a_1260_);
lean_dec(v_a_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = l_Lean_Expr_getAppFn(v_a_1250_);
lean_inc_ref(v___x_1262_);
v___x_1263_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1262_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; uint8_t v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = lean_unbox(v_a_1264_);
lean_dec(v_a_1264_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1262_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v_dummy_1268_; lean_object* v_nargs_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; size_t v_sz_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v_dummy_1268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1269_ = l_Lean_Expr_getAppNumArgs(v_a_1250_);
lean_inc(v_nargs_1269_);
v___x_1270_ = lean_mk_array(v_nargs_1269_, v_dummy_1268_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_sub(v_nargs_1269_, v___x_1271_);
lean_dec(v_nargs_1269_);
lean_inc_n(v_a_1250_, 2);
v___x_1273_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1250_, v___x_1270_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_snd_1231_);
lean_ctor_set(v___x_1274_, 1, v___x_1267_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_fst_1230_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v_sz_1276_ = lean_array_size(v___x_1273_);
v___x_1277_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1208_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1250_, v_ctx_1208_, v___x_1262_, v___x_1273_, v_sz_1276_, v___x_1277_, v___x_1275_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec_ref(v___x_1273_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_snd_1280_; lean_object* v_fst_1281_; lean_object* v_fst_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v_snd_1280_ = lean_ctor_get(v_a_1279_, 1);
lean_inc(v_snd_1280_);
v_fst_1281_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_fst_1281_);
lean_dec(v_a_1279_);
v_fst_1282_ = lean_ctor_get(v_snd_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_snd_1280_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_snd_1280_, 1);
lean_dec(v_unused_1290_);
v___x_1284_ = v_snd_1280_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_fst_1282_);
lean_dec(v_snd_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_fst_1282_);
lean_ctor_set(v___x_1284_, 0, v_fst_1281_);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_fst_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_fst_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v_a_1237_ = v___x_1287_;
goto v___jp_1236_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_del_object(v___x_1233_);
lean_dec_ref(v_ctx_1208_);
v_a_1291_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1278_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1278_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_dec_ref(v___x_1262_);
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v___x_1262_);
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v___x_1262_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec_ref(v_ctx_1208_);
v_a_1299_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1263_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1263_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_fst_1230_);
lean_ctor_set(v___x_1307_, 1, v_snd_1231_);
v_a_1237_ = v___x_1307_;
goto v___jp_1236_;
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec_ref(v_ctx_1208_);
v_a_1308_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1259_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1259_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec_ref(v_ctx_1208_);
v_a_1316_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1254_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1254_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
goto v___jp_1244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object* v_ctx_1329_, lean_object* v_as_1330_, lean_object* v_sz_1331_, lean_object* v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1331_);
lean_dec(v_sz_1331_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1329_, v_as_1330_, v_sz_boxed_1345_, v_i_boxed_1346_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v_as_1330_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1348_, lean_object* v_as_1349_, size_t v_sz_1350_, size_t v_i_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_usize_dec_lt(v_i_1351_, v_sz_1350_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref(v_ctx_1348_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_b_1352_);
return v___x_1365_;
}
else
{
lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1467_; 
v_snd_1366_ = lean_ctor_get(v_b_1352_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_b_1352_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_b_1352_, 0);
lean_dec(v_unused_1468_);
v___x_1368_ = v_b_1352_;
v_isShared_1369_ = v_isSharedCheck_1467_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_dec(v_b_1352_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1467_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1466_; 
v_fst_1370_ = lean_ctor_get(v_snd_1366_, 0);
v_snd_1371_ = lean_ctor_get(v_snd_1366_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_snd_1366_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1373_ = v_snd_1366_;
v_isShared_1374_ = v_isSharedCheck_1466_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_snd_1366_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1466_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v_a_1377_; lean_object* v_a_1390_; uint8_t v___y_1392_; uint8_t v___x_1464_; 
v___x_1375_ = lean_box(0);
v_a_1390_ = lean_array_uget_borrowed(v_as_1349_, v_i_1351_);
v___x_1464_ = l_Lean_Expr_isApp(v_a_1390_);
if (v___x_1464_ == 0)
{
v___y_1392_ = v___x_1464_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_Expr_isEq(v_a_1390_);
if (v___x_1465_ == 0)
{
v___y_1392_ = v___x_1464_;
goto v___jp_1391_;
}
else
{
goto v___jp_1384_;
}
}
v___jp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_a_1377_);
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1379_ = v___x_1373_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_a_1377_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1351_, v___x_1380_);
v_i_1351_ = v___x_1381_;
v_b_1352_ = v___x_1379_;
goto _start;
}
}
v___jp_1384_:
{
lean_object* v___x_1386_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v_snd_1371_);
lean_ctor_set(v___x_1368_, 0, v_fst_1370_);
v___x_1386_ = v___x_1368_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1371_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v_a_1377_ = v___x_1386_;
goto v___jp_1376_;
}
}
v___jp_1388_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_fst_1370_);
lean_ctor_set(v___x_1389_, 1, v_snd_1371_);
v_a_1377_ = v___x_1389_;
goto v___jp_1376_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
goto v___jp_1384_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_Expr_isHEq(v_a_1390_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_del_object(v___x_1368_);
lean_inc(v_a_1390_);
v___x_1394_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1390_, v___y_1353_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; uint8_t v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_fst_1370_);
lean_ctor_set(v___x_1397_, 1, v_snd_1371_);
v_a_1377_ = v___x_1397_;
goto v___jp_1376_;
}
else
{
lean_object* v_isInterpreted_1398_; lean_object* v___x_1399_; 
v_isInterpreted_1398_ = lean_ctor_get(v_ctx_1348_, 0);
lean_inc_ref(v_isInterpreted_1398_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v_a_1390_);
v___x_1399_ = lean_apply_12(v_isInterpreted_1398_, v_a_1390_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, lean_box(0));
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; uint8_t v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1399_);
v___x_1401_ = lean_unbox(v_a_1400_);
lean_dec(v_a_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = l_Lean_Expr_getAppFn(v_a_1390_);
lean_inc_ref(v___x_1402_);
v___x_1403_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1402_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; uint8_t v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = lean_unbox(v_a_1404_);
lean_dec(v_a_1404_);
if (v___x_1405_ == 0)
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1402_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v_dummy_1408_; lean_object* v_nargs_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v_dummy_1408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1409_ = l_Lean_Expr_getAppNumArgs(v_a_1390_);
lean_inc(v_nargs_1409_);
v___x_1410_ = lean_mk_array(v_nargs_1409_, v_dummy_1408_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_sub(v_nargs_1409_, v___x_1411_);
lean_dec(v_nargs_1409_);
lean_inc_n(v_a_1390_, 2);
v___x_1413_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1390_, v___x_1410_, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_snd_1371_);
lean_ctor_set(v___x_1414_, 1, v___x_1407_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_fst_1370_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v_sz_1416_ = lean_array_size(v___x_1413_);
v___x_1417_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1348_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1390_, v_ctx_1348_, v___x_1402_, v___x_1413_, v_sz_1416_, v___x_1417_, v___x_1415_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___x_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_snd_1420_; lean_object* v_fst_1421_; lean_object* v_fst_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v_snd_1420_ = lean_ctor_get(v_a_1419_, 1);
lean_inc(v_snd_1420_);
v_fst_1421_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_fst_1421_);
lean_dec(v_a_1419_);
v_fst_1422_ = lean_ctor_get(v_snd_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_snd_1420_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_snd_1420_, 1);
lean_dec(v_unused_1430_);
v___x_1424_ = v_snd_1420_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_fst_1422_);
lean_dec(v_snd_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v_fst_1422_);
lean_ctor_set(v___x_1424_, 0, v_fst_1421_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_fst_1421_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_fst_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v_a_1377_ = v___x_1427_;
goto v___jp_1376_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_del_object(v___x_1373_);
lean_dec_ref(v_ctx_1348_);
v_a_1431_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1418_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1418_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_dec_ref(v___x_1402_);
goto v___jp_1388_;
}
}
else
{
lean_dec_ref(v___x_1402_);
goto v___jp_1388_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1373_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_ctx_1348_);
v_a_1439_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1403_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1403_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_fst_1370_);
lean_ctor_set(v___x_1447_, 1, v_snd_1371_);
v_a_1377_ = v___x_1447_;
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1373_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_ctx_1348_);
v_a_1448_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1399_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1399_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_del_object(v___x_1373_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_ctx_1348_);
v_a_1456_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1394_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1394_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
goto v___jp_1384_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object* v_ctx_1469_, lean_object* v_as_1470_, lean_object* v_sz_1471_, lean_object* v_i_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
size_t v_sz_boxed_1485_; size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_sz_boxed_1485_ = lean_unbox_usize(v_sz_1471_);
lean_dec(v_sz_1471_);
v_i_boxed_1486_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1469_, v_as_1470_, v_sz_boxed_1485_, v_i_boxed_1486_, v_b_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v_as_1470_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref(v_ctx_1488_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_b_1492_);
return v___x_1505_;
}
else
{
lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1607_; 
v_snd_1506_ = lean_ctor_get(v_b_1492_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_b_1492_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_b_1492_, 0);
lean_dec(v_unused_1608_);
v___x_1508_ = v_b_1492_;
v_isShared_1509_ = v_isSharedCheck_1607_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_dec(v_b_1492_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1607_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_fst_1510_; lean_object* v_snd_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1606_; 
v_fst_1510_ = lean_ctor_get(v_snd_1506_, 0);
v_snd_1511_ = lean_ctor_get(v_snd_1506_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_snd_1506_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1513_ = v_snd_1506_;
v_isShared_1514_ = v_isSharedCheck_1606_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_snd_1511_);
lean_inc(v_fst_1510_);
lean_dec(v_snd_1506_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1606_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v_a_1517_; lean_object* v_a_1530_; uint8_t v___y_1532_; uint8_t v___x_1604_; 
v___x_1515_ = lean_box(0);
v_a_1530_ = lean_array_uget_borrowed(v_as_1489_, v_i_1491_);
v___x_1604_ = l_Lean_Expr_isApp(v_a_1530_);
if (v___x_1604_ == 0)
{
v___y_1532_ = v___x_1604_;
goto v___jp_1531_;
}
else
{
uint8_t v___x_1605_; 
v___x_1605_ = l_Lean_Expr_isEq(v_a_1530_);
if (v___x_1605_ == 0)
{
v___y_1532_ = v___x_1604_;
goto v___jp_1531_;
}
else
{
goto v___jp_1524_;
}
}
v___jp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v_a_1517_);
lean_ctor_set(v___x_1513_, 0, v___x_1515_);
v___x_1519_ = v___x_1513_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_a_1517_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_add(v_i_1491_, v___x_1520_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1488_, v_as_1489_, v_sz_1490_, v___x_1521_, v___x_1519_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1522_;
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v_snd_1511_);
lean_ctor_set(v___x_1508_, 0, v_fst_1510_);
v___x_1526_ = v___x_1508_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_fst_1510_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_snd_1511_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
v_a_1517_ = v___x_1526_;
goto v___jp_1516_;
}
}
v___jp_1528_:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_fst_1510_);
lean_ctor_set(v___x_1529_, 1, v_snd_1511_);
v_a_1517_ = v___x_1529_;
goto v___jp_1516_;
}
v___jp_1531_:
{
if (v___y_1532_ == 0)
{
goto v___jp_1524_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = l_Lean_Expr_isHEq(v_a_1530_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_del_object(v___x_1508_);
lean_inc(v_a_1530_);
v___x_1534_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1530_, v___y_1493_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; uint8_t v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = lean_unbox(v_a_1535_);
lean_dec(v_a_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_fst_1510_);
lean_ctor_set(v___x_1537_, 1, v_snd_1511_);
v_a_1517_ = v___x_1537_;
goto v___jp_1516_;
}
else
{
lean_object* v_isInterpreted_1538_; lean_object* v___x_1539_; 
v_isInterpreted_1538_ = lean_ctor_get(v_ctx_1488_, 0);
lean_inc_ref(v_isInterpreted_1538_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc(v_a_1530_);
v___x_1539_ = lean_apply_12(v_isInterpreted_1538_, v_a_1530_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, lean_box(0));
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; uint8_t v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_Expr_getAppFn(v_a_1530_);
lean_inc_ref(v___x_1542_);
v___x_1543_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1542_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; uint8_t v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v_dummy_1548_; lean_object* v_nargs_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; size_t v_sz_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v_dummy_1548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1549_ = l_Lean_Expr_getAppNumArgs(v_a_1530_);
lean_inc(v_nargs_1549_);
v___x_1550_ = lean_mk_array(v_nargs_1549_, v_dummy_1548_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_sub(v_nargs_1549_, v___x_1551_);
lean_dec(v_nargs_1549_);
lean_inc_n(v_a_1530_, 2);
v___x_1553_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1530_, v___x_1550_, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_snd_1511_);
lean_ctor_set(v___x_1554_, 1, v___x_1547_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_fst_1510_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v_sz_1556_ = lean_array_size(v___x_1553_);
v___x_1557_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1488_);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1530_, v_ctx_1488_, v___x_1542_, v___x_1553_, v_sz_1556_, v___x_1557_, v___x_1555_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_snd_1560_; lean_object* v_fst_1561_; lean_object* v_fst_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
v_snd_1560_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1560_);
v_fst_1561_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_fst_1561_);
lean_dec(v_a_1559_);
v_fst_1562_ = lean_ctor_get(v_snd_1560_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_snd_1560_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_snd_1560_, 1);
lean_dec(v_unused_1570_);
v___x_1564_ = v_snd_1560_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_fst_1562_);
lean_dec(v_snd_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v_fst_1562_);
lean_ctor_set(v___x_1564_, 0, v_fst_1561_);
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_fst_1561_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_fst_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
v_a_1517_ = v___x_1567_;
goto v___jp_1516_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1513_);
lean_dec_ref(v_ctx_1488_);
v_a_1571_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1558_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1558_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_dec_ref(v___x_1542_);
goto v___jp_1528_;
}
}
else
{
lean_dec_ref(v___x_1542_);
goto v___jp_1528_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v___x_1542_);
lean_del_object(v___x_1513_);
lean_dec(v_snd_1511_);
lean_dec(v_fst_1510_);
lean_dec_ref(v_ctx_1488_);
v_a_1579_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1543_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1543_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_fst_1510_);
lean_ctor_set(v___x_1587_, 1, v_snd_1511_);
v_a_1517_ = v___x_1587_;
goto v___jp_1516_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_del_object(v___x_1513_);
lean_dec(v_snd_1511_);
lean_dec(v_fst_1510_);
lean_dec_ref(v_ctx_1488_);
v_a_1588_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1539_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1539_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1513_);
lean_dec(v_snd_1511_);
lean_dec(v_fst_1510_);
lean_dec_ref(v_ctx_1488_);
v_a_1596_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1534_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1534_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
goto v___jp_1524_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object* v_ctx_1609_, lean_object* v_as_1610_, lean_object* v_sz_1611_, lean_object* v_i_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
size_t v_sz_boxed_1625_; size_t v_i_boxed_1626_; lean_object* v_res_1627_; 
v_sz_boxed_1625_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1626_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1609_, v_as_1610_, v_sz_boxed_1625_, v_i_boxed_1626_, v_b_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v_as_1610_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1628_, lean_object* v_ctx_1629_, lean_object* v_n_1630_, lean_object* v_b_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (lean_obj_tag(v_n_1630_) == 0)
{
lean_object* v_cs_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; size_t v_sz_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v_cs_1643_ = lean_ctor_get(v_n_1630_, 0);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_b_1631_);
v_sz_1646_ = lean_array_size(v_cs_1643_);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1628_, v_ctx_1629_, v_cs_1643_, v_sz_1646_, v___x_1647_, v___x_1645_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1663_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_fst_1653_; 
v_fst_1653_ = lean_ctor_get(v_a_1649_, 0);
if (lean_obj_tag(v_fst_1653_) == 0)
{
lean_object* v_snd_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_snd_1654_ = lean_ctor_get(v_a_1649_, 1);
lean_inc(v_snd_1654_);
lean_dec(v_a_1649_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_snd_1654_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1655_);
v___x_1657_ = v___x_1651_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
else
{
lean_object* v_val_1659_; lean_object* v___x_1661_; 
lean_inc_ref(v_fst_1653_);
lean_dec(v_a_1649_);
v_val_1659_ = lean_ctor_get(v_fst_1653_, 0);
lean_inc(v_val_1659_);
lean_dec_ref(v_fst_1653_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v_val_1659_);
v___x_1661_ = v___x_1651_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_val_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1648_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1648_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_vs_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; size_t v_sz_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
v_vs_1672_ = lean_ctor_get(v_n_1630_, 0);
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_b_1631_);
v_sz_1675_ = lean_array_size(v_vs_1672_);
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1629_, v_vs_1672_, v_sz_1675_, v___x_1676_, v___x_1674_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1692_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_fst_1682_; 
v_fst_1682_ = lean_ctor_get(v_a_1678_, 0);
if (lean_obj_tag(v_fst_1682_) == 0)
{
lean_object* v_snd_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v_snd_1683_ = lean_ctor_get(v_a_1678_, 1);
lean_inc(v_snd_1683_);
lean_dec(v_a_1678_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_snd_1683_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1684_);
v___x_1686_ = v___x_1680_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
else
{
lean_object* v_val_1688_; lean_object* v___x_1690_; 
lean_inc_ref(v_fst_1682_);
lean_dec(v_a_1678_);
v_val_1688_ = lean_ctor_get(v_fst_1682_, 0);
lean_inc(v_val_1688_);
lean_dec_ref(v_fst_1682_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_val_1688_);
v___x_1690_ = v___x_1680_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_val_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1677_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1677_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1701_, lean_object* v_ctx_1702_, lean_object* v_as_1703_, size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_b_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref(v_ctx_1702_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1706_);
return v___x_1719_;
}
else
{
lean_object* v_snd_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1754_; 
v_snd_1720_ = lean_ctor_get(v_b_1706_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_b_1706_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_b_1706_, 0);
lean_dec(v_unused_1755_);
v___x_1722_ = v_b_1706_;
v_isShared_1723_ = v_isSharedCheck_1754_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_snd_1720_);
lean_dec(v_b_1706_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1754_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_array_uget_borrowed(v_as_1703_, v_i_1705_);
lean_inc(v_snd_1720_);
lean_inc_ref(v_ctx_1702_);
v___x_1725_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1701_, v_ctx_1702_, v_a_1724_, v_snd_1720_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1745_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1745_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1745_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
if (lean_obj_tag(v_a_1726_) == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_dec_ref(v_ctx_1702_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1726_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1730_);
v___x_1732_ = v___x_1722_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_snd_1720_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1732_);
v___x_1734_ = v___x_1728_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_del_object(v___x_1728_);
lean_dec(v_snd_1720_);
v_a_1737_ = lean_ctor_get(v_a_1726_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v_a_1726_);
v___x_1738_ = lean_box(0);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_a_1737_);
lean_ctor_set(v___x_1722_, 0, v___x_1738_);
v___x_1740_ = v___x_1722_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1737_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1705_, v___x_1741_);
v_i_1705_ = v___x_1742_;
v_b_1706_ = v___x_1740_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_del_object(v___x_1722_);
lean_dec(v_snd_1720_);
lean_dec_ref(v_ctx_1702_);
v_a_1746_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1725_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1725_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1756_ = _args[0];
lean_object* v_ctx_1757_ = _args[1];
lean_object* v_as_1758_ = _args[2];
lean_object* v_sz_1759_ = _args[3];
lean_object* v_i_1760_ = _args[4];
lean_object* v_b_1761_ = _args[5];
lean_object* v___y_1762_ = _args[6];
lean_object* v___y_1763_ = _args[7];
lean_object* v___y_1764_ = _args[8];
lean_object* v___y_1765_ = _args[9];
lean_object* v___y_1766_ = _args[10];
lean_object* v___y_1767_ = _args[11];
lean_object* v___y_1768_ = _args[12];
lean_object* v___y_1769_ = _args[13];
lean_object* v___y_1770_ = _args[14];
lean_object* v___y_1771_ = _args[15];
lean_object* v___y_1772_ = _args[16];
_start:
{
size_t v_sz_boxed_1773_; size_t v_i_boxed_1774_; lean_object* v_res_1775_; 
v_sz_boxed_1773_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1774_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1756_, v_ctx_1757_, v_as_1758_, v_sz_boxed_1773_, v_i_boxed_1774_, v_b_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v_as_1758_);
lean_dec_ref(v_init_1756_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1776_, lean_object* v_ctx_1777_, lean_object* v_n_1778_, lean_object* v_b_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1776_, v_ctx_1777_, v_n_1778_, v_b_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v_n_1778_);
lean_dec_ref(v_init_1776_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1792_, lean_object* v_t_1793_, lean_object* v_init_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_root_1806_; lean_object* v_tail_1807_; lean_object* v___x_1808_; 
v_root_1806_ = lean_ctor_get(v_t_1793_, 0);
v_tail_1807_ = lean_ctor_get(v_t_1793_, 1);
lean_inc_ref(v_ctx_1792_);
lean_inc_ref(v_init_1794_);
v___x_1808_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1794_, v_ctx_1792_, v_root_1806_, v_init_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v_init_1794_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1845_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1845_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1845_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; 
lean_dec_ref(v_ctx_1792_);
v_a_1813_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_a_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1811_);
v_a_1817_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v_a_1809_);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v_a_1817_);
v_sz_1820_ = lean_array_size(v_tail_1807_);
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1792_, v_tail_1807_, v_sz_1820_, v___x_1821_, v___x_1819_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1836_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1836_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1836_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_fst_1827_; 
v_fst_1827_ = lean_ctor_get(v_a_1823_, 0);
if (lean_obj_tag(v_fst_1827_) == 0)
{
lean_object* v_snd_1828_; lean_object* v___x_1830_; 
v_snd_1828_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_snd_1828_);
lean_dec(v_a_1823_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_snd_1828_);
v___x_1830_ = v___x_1825_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_snd_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
lean_object* v_val_1832_; lean_object* v___x_1834_; 
lean_inc_ref(v_fst_1827_);
lean_dec(v_a_1823_);
v_val_1832_ = lean_ctor_get(v_fst_1827_, 0);
lean_inc(v_val_1832_);
lean_dec_ref(v_fst_1827_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_val_1832_);
v___x_1834_ = v___x_1825_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_val_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_a_1837_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1822_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1822_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v_ctx_1792_);
v_a_1846_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1808_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1808_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1854_, lean_object* v_t_1855_, lean_object* v_init_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1854_, v_t_1855_, v_init_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v_t_1855_);
return v_res_1868_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1874_ = l_Lean_Name_append(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1875_, size_t v_i_1876_, size_t v_stop_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_a_1891_; uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_eq(v_i_1876_, v_stop_1877_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_array_uget_borrowed(v_as_1875_, v_i_1876_);
v___x_1897_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1896_, v___y_1879_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
if (v___x_1899_ == 0)
{
if (lean_obj_tag(v___x_1896_) == 2)
{
lean_object* v_a_1900_; lean_object* v_b_1901_; lean_object* v_eq_1902_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v_options_1958_; uint8_t v_hasTrace_1959_; 
v_a_1900_ = lean_ctor_get(v___x_1896_, 0);
v_b_1901_ = lean_ctor_get(v___x_1896_, 1);
v_eq_1902_ = lean_ctor_get(v___x_1896_, 3);
v_options_1958_ = lean_ctor_get(v___y_1887_, 2);
v_hasTrace_1959_ = lean_ctor_get_uint8(v_options_1958_, sizeof(void*)*1);
if (v_hasTrace_1959_ == 0)
{
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
goto v___jp_1926_;
}
else
{
lean_object* v_inheritedTraceOptions_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_inheritedTraceOptions_1960_ = lean_ctor_get(v___y_1887_, 13);
v___x_1961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1962_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1960_, v_options_1958_, v___x_1962_);
if (v___x_1963_ == 0)
{
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref(v_eq_1902_);
v___x_1964_ = l_Lean_MessageData_ofExpr(v_eq_1902_);
v___x_1965_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1961_, v___x_1964_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref(v___x_1965_);
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_b_1878_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
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
}
v___jp_1903_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_box(0);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1910_);
lean_inc(v___y_1905_);
lean_inc_ref(v_eq_1902_);
v___x_1916_ = lean_grind_internalize(v_eq_1902_, v___y_1914_, v___x_1915_, v___y_1905_, v___y_1910_, v___y_1912_, v___y_1908_, v___y_1911_, v___y_1909_, v___y_1906_, v___y_1907_, v___y_1904_, v___y_1913_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref(v___x_1916_);
lean_inc_ref(v___x_1896_);
v___x_1917_ = lean_array_push(v_b_1878_, v___x_1896_);
v_a_1891_ = v___x_1917_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_b_1878_);
v_a_1918_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
v___jp_1926_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1900_, v___y_1927_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v___x_1939_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1901_, v___y_1927_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; uint8_t v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = lean_nat_dec_le(v_a_1938_, v_a_1940_);
if (v___x_1941_ == 0)
{
lean_dec(v_a_1940_);
v___y_1904_ = v___y_1935_;
v___y_1905_ = v___y_1927_;
v___y_1906_ = v___y_1933_;
v___y_1907_ = v___y_1934_;
v___y_1908_ = v___y_1930_;
v___y_1909_ = v___y_1932_;
v___y_1910_ = v___y_1928_;
v___y_1911_ = v___y_1931_;
v___y_1912_ = v___y_1929_;
v___y_1913_ = v___y_1936_;
v___y_1914_ = v_a_1938_;
goto v___jp_1903_;
}
else
{
lean_dec(v_a_1938_);
v___y_1904_ = v___y_1935_;
v___y_1905_ = v___y_1927_;
v___y_1906_ = v___y_1933_;
v___y_1907_ = v___y_1934_;
v___y_1908_ = v___y_1930_;
v___y_1909_ = v___y_1932_;
v___y_1910_ = v___y_1928_;
v___y_1911_ = v___y_1931_;
v___y_1912_ = v___y_1929_;
v___y_1913_ = v___y_1936_;
v___y_1914_ = v_a_1940_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1938_);
lean_dec_ref(v_b_1878_);
v_a_1942_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1939_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1939_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_b_1878_);
v_a_1950_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1937_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1937_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
else
{
v_a_1891_ = v_b_1878_;
goto v___jp_1890_;
}
}
else
{
v_a_1891_ = v_b_1878_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_b_1878_);
v_a_1974_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1897_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1897_);
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
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_b_1878_);
return v___x_1982_;
}
v___jp_1890_:
{
size_t v___x_1892_; size_t v___x_1893_; 
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1876_, v___x_1892_);
v_i_1876_ = v___x_1893_;
v_b_1878_ = v_a_1891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_1983_, lean_object* v_i_1984_, lean_object* v_stop_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
size_t v_i_boxed_1998_; size_t v_stop_boxed_1999_; lean_object* v_res_2000_; 
v_i_boxed_1998_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_stop_boxed_1999_ = lean_unbox_usize(v_stop_1985_);
lean_dec(v_stop_1985_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_1983_, v_i_boxed_1998_, v_stop_boxed_1999_, v_b_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v_as_1983_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2003_, lean_object* v_start_2004_, lean_object* v_stop_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2018_ = lean_nat_dec_lt(v_start_2004_, v_stop_2005_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_array_get_size(v_as_2003_);
v___x_2021_ = lean_nat_dec_le(v_stop_2005_, v___x_2020_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_nat_dec_lt(v_start_2004_, v___x_2020_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2017_);
return v___x_2023_;
}
else
{
size_t v___x_2024_; size_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_usize_of_nat(v_start_2004_);
v___x_2025_ = lean_usize_of_nat(v___x_2020_);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2003_, v___x_2024_, v___x_2025_, v___x_2017_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2026_;
}
}
else
{
size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_usize_of_nat(v_start_2004_);
v___x_2028_ = lean_usize_of_nat(v_stop_2005_);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2003_, v___x_2027_, v___x_2028_, v___x_2017_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2030_, lean_object* v_start_2031_, lean_object* v_stop_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2030_, v_start_2031_, v_stop_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec(v_stop_2032_);
lean_dec(v_start_2031_);
lean_dec_ref(v_as_2030_);
return v_res_2044_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_unsigned_to_nat(16u);
v___x_2047_ = lean_mk_array(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2062_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2276_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2276_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2276_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v_mbtc_2076_; 
v_mbtc_2076_ = lean_ctor_get_uint8(v_a_2072_, sizeof(void*)*13 + 18);
lean_dec(v_a_2072_);
if (v_mbtc_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
lean_dec_ref(v_ctx_2059_);
v___x_2077_ = lean_box(v_mbtc_2076_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
else
{
lean_object* v___x_2081_; 
lean_del_object(v___x_2074_);
v___x_2081_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2060_, v_a_2062_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2275_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2275_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2275_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_unbox(v_a_2082_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v_toGoalState_2088_; lean_object* v_exprs_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_del_object(v___x_2084_);
v___x_2087_ = lean_st_ref_get(v_a_2060_);
v_toGoalState_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc_ref(v_toGoalState_2088_);
lean_dec(v___x_2087_);
v_exprs_2089_ = lean_ctor_get(v_toGoalState_2088_, 2);
lean_inc_ref(v_exprs_2089_);
lean_dec_ref(v_toGoalState_2088_);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2092_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2059_, v_exprs_2089_, v___x_2091_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec_ref(v_exprs_2089_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2261_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2261_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2261_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_snd_2097_; lean_object* v_size_2098_; lean_object* v_buckets_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2260_; 
v_snd_2097_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_snd_2097_);
lean_dec(v_a_2093_);
v_size_2098_ = lean_ctor_get(v_snd_2097_, 0);
v_buckets_2099_ = lean_ctor_get(v_snd_2097_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_snd_2097_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2101_ = v_snd_2097_;
v_isShared_2102_ = v_isSharedCheck_2260_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_buckets_2099_);
lean_inc(v_size_2098_);
lean_dec(v_snd_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2260_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_eq(v_size_2098_, v___x_2090_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2095_);
lean_dec(v_a_2082_);
v___x_2104_ = lean_st_ref_get(v_a_2060_);
v___x_2105_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2062_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___y_2108_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2164_; lean_object* v_toGoalState_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2247_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v_toGoalState_2170_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2104_, 1);
lean_dec(v_unused_2248_);
v___x_2172_ = v___x_2104_;
v_isShared_2173_ = v_isSharedCheck_2247_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_toGoalState_2170_);
lean_dec(v___x_2104_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2247_;
goto v_resetjp_2171_;
}
v___jp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_array_get_size(v___y_2108_);
v___x_2110_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2108_, v___x_2090_, v___x_2109_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec_ref(v___y_2108_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2142_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2142_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2142_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_array_get_size(v_a_2111_);
v___x_2116_ = lean_nat_dec_eq(v___x_2115_, v___x_2090_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
lean_del_object(v___x_2113_);
v___x_2117_ = lean_box(0);
v_sz_2118_ = lean_array_size(v_a_2111_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2111_, v_sz_2118_, v___x_2119_, v___x_2117_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2111_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2120_, 0);
lean_dec(v_unused_2129_);
v___x_2122_ = v___x_2120_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v___x_2120_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_box(v_mbtc_2076_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2120_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2120_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
lean_dec(v_a_2111_);
v___x_2138_ = lean_box(v___x_2103_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2138_);
v___x_2140_ = v___x_2113_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
v_a_2143_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2110_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2110_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
v___jp_2151_:
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec(v___y_2152_);
v___y_2108_ = v___x_2156_;
goto v___jp_2107_;
}
v___jp_2157_:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_nat_dec_le(v___y_2161_, v___y_2160_);
if (v___x_2162_ == 0)
{
lean_dec(v___y_2160_);
lean_inc(v___y_2161_);
v___y_2152_ = v___y_2158_;
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v___y_2155_ = v___y_2161_;
goto v___jp_2151_;
}
else
{
v___y_2152_ = v___y_2158_;
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v___y_2155_ = v___y_2160_;
goto v___jp_2151_;
}
}
v___jp_2163_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_array_get_size(v___y_2164_);
v___x_2166_ = lean_nat_dec_eq(v___x_2165_, v___x_2090_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_sub(v___x_2165_, v___x_2167_);
v___x_2169_ = lean_nat_dec_le(v___x_2090_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_inc(v___x_2168_);
v___y_2158_ = v___x_2165_;
v___y_2159_ = v___y_2164_;
v___y_2160_ = v___x_2168_;
v___y_2161_ = v___x_2168_;
goto v___jp_2157_;
}
else
{
v___y_2158_ = v___x_2165_;
v___y_2159_ = v___y_2164_;
v___y_2160_ = v___x_2168_;
v___y_2161_ = v___x_2090_;
goto v___jp_2157_;
}
}
else
{
v___y_2108_ = v___y_2164_;
goto v___jp_2107_;
}
}
v_resetjp_2171_:
{
lean_object* v_split_2174_; lean_object* v_splits_2175_; lean_object* v_num_2176_; uint8_t v___x_2177_; 
v_split_2174_ = lean_ctor_get(v_toGoalState_2170_, 14);
lean_inc_ref(v_split_2174_);
lean_dec_ref(v_toGoalState_2170_);
v_splits_2175_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_splits_2175_);
lean_dec(v_a_2106_);
v_num_2176_ = lean_ctor_get(v_split_2174_, 0);
lean_inc(v_num_2176_);
lean_dec_ref(v_split_2174_);
v___x_2177_ = lean_nat_dec_lt(v_splits_2175_, v_num_2176_);
lean_dec(v_num_2176_);
lean_dec(v_splits_2175_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
lean_del_object(v___x_2172_);
lean_del_object(v___x_2101_);
v___x_2178_ = lean_mk_empty_array_with_capacity(v_size_2098_);
lean_dec(v_size_2098_);
v___x_2179_ = lean_array_get_size(v_buckets_2099_);
v___x_2180_ = lean_nat_dec_lt(v___x_2090_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v_buckets_2099_);
v___y_2164_ = v___x_2178_;
goto v___jp_2163_;
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_nat_dec_le(v___x_2179_, v___x_2179_);
if (v___x_2181_ == 0)
{
if (v___x_2180_ == 0)
{
lean_dec_ref(v_buckets_2099_);
v___y_2164_ = v___x_2178_;
goto v___jp_2163_;
}
else
{
size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2179_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2099_, v___x_2182_, v___x_2183_, v___x_2178_);
lean_dec_ref(v_buckets_2099_);
v___y_2164_ = v___x_2184_;
goto v___jp_2163_;
}
}
else
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2179_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2099_, v___x_2185_, v___x_2186_, v___x_2178_);
lean_dec_ref(v_buckets_2099_);
v___y_2164_ = v___x_2187_;
goto v___jp_2163_;
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v_buckets_2099_);
lean_dec(v_size_2098_);
v___x_2188_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2062_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v___x_2188_);
v___x_2190_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2064_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2230_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2230_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2230_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
uint8_t v___x_2195_; 
v___x_2195_ = lean_unbox(v_a_2191_);
lean_dec(v_a_2191_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_dec(v_a_2189_);
lean_del_object(v___x_2172_);
lean_del_object(v___x_2101_);
v___x_2196_ = lean_box(v___x_2103_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v_splits_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_del_object(v___x_2193_);
v_splits_2200_ = lean_ctor_get(v_a_2189_, 0);
lean_inc(v_splits_2200_);
lean_dec(v_a_2189_);
v___x_2201_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2202_ = l_Nat_reprFast(v_splits_2200_);
v___x_2203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = l_Lean_MessageData_ofFormat(v___x_2203_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 7);
lean_ctor_set(v___x_2172_, 1, v___x_2204_);
lean_ctor_set(v___x_2172_, 0, v___x_2201_);
v___x_2206_ = v___x_2172_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 7);
lean_ctor_set(v___x_2101_, 1, v___x_2207_);
lean_ctor_set(v___x_2101_, 0, v___x_2206_);
v___x_2209_ = v___x_2101_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Meta_Sym_reportIssue(v___x_2209_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2218_; 
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v___x_2210_, 0);
lean_dec(v_unused_2219_);
v___x_2212_ = v___x_2210_;
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
else
{
lean_dec(v___x_2210_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_box(v___x_2103_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2210_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2210_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2189_);
lean_del_object(v___x_2172_);
lean_del_object(v___x_2101_);
v_a_2231_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2190_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2190_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2172_);
lean_del_object(v___x_2101_);
v_a_2239_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2188_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2188_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v___x_2104_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_buckets_2099_);
lean_dec(v_size_2098_);
v_a_2249_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2105_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2105_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v___x_2258_; 
lean_del_object(v___x_2101_);
lean_dec_ref(v_buckets_2099_);
lean_dec(v_size_2098_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v_a_2082_);
v___x_2258_ = v___x_2095_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2082_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_2082_);
v_a_2262_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2092_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2092_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
lean_dec(v_a_2082_);
lean_dec_ref(v_ctx_2059_);
v___x_2270_ = 0;
v___x_2271_ = lean_box(v___x_2270_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2271_);
v___x_2273_ = v___x_2084_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2059_);
return v___x_2081_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_ctx_2059_);
v_a_2277_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2071_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2071_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Meta_Grind_mbtc(v_ctx_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec(v_a_2286_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2298_, v_msg_2299_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2312_, lean_object* v_msg_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2312_, v_msg_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec(v___y_2314_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2326_, lean_object* v_m_2327_, lean_object* v_a_2328_, lean_object* v_b_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2327_, v_a_2328_, v_b_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2331_, lean_object* v_m_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2332_, v_a_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2335_, lean_object* v_m_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2335_, v_m_2336_, v_a_2337_);
lean_dec_ref(v_a_2337_);
lean_dec_ref(v_m_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2339_, lean_object* v_val_2340_, lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v_as_2343_, lean_object* v_as_x27_2344_, lean_object* v_b_2345_, lean_object* v_a_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2339_, v_val_2340_, v___x_2341_, v___x_2342_, v_as_x27_2344_, v_b_2345_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2359_ = _args[0];
lean_object* v_val_2360_ = _args[1];
lean_object* v___x_2361_ = _args[2];
lean_object* v___x_2362_ = _args[3];
lean_object* v_as_2363_ = _args[4];
lean_object* v_as_x27_2364_ = _args[5];
lean_object* v_b_2365_ = _args[6];
lean_object* v_a_2366_ = _args[7];
lean_object* v___y_2367_ = _args[8];
lean_object* v___y_2368_ = _args[9];
lean_object* v___y_2369_ = _args[10];
lean_object* v___y_2370_ = _args[11];
lean_object* v___y_2371_ = _args[12];
lean_object* v___y_2372_ = _args[13];
lean_object* v___y_2373_ = _args[14];
lean_object* v___y_2374_ = _args[15];
lean_object* v___y_2375_ = _args[16];
lean_object* v___y_2376_ = _args[17];
lean_object* v___y_2377_ = _args[18];
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2359_, v_val_2360_, v___x_2361_, v___x_2362_, v_as_2363_, v_as_x27_2364_, v_b_2365_, v_a_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec(v_as_x27_2364_);
lean_dec(v_as_2363_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2379_, lean_object* v_m_2380_, lean_object* v_a_2381_, lean_object* v_b_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2380_, v_a_2381_, v_b_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2384_, lean_object* v_as_2385_, lean_object* v_lo_2386_, lean_object* v_hi_2387_, lean_object* v_w_2388_, lean_object* v_hlo_2389_, lean_object* v_hhi_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2384_, v_as_2385_, v_lo_2386_, v_hi_2387_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2392_, lean_object* v_as_2393_, lean_object* v_lo_2394_, lean_object* v_hi_2395_, lean_object* v_w_2396_, lean_object* v_hlo_2397_, lean_object* v_hhi_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2392_, v_as_2393_, v_lo_2394_, v_hi_2395_, v_w_2396_, v_hlo_2397_, v_hhi_2398_);
lean_dec(v_hi_2395_);
lean_dec(v_n_2392_);
return v_res_2399_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2400_, lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2401_, v_x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2404_, lean_object* v_a_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2404_, v_a_2405_, v_x_2406_);
lean_dec(v_x_2406_);
lean_dec_ref(v_a_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2409_, lean_object* v_data_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2412_, lean_object* v_a_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2413_, v_x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_a_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2416_, v_a_2417_, v_x_2418_);
lean_dec(v_x_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2421_, v_x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2424_, lean_object* v_a_2425_, lean_object* v_x_2426_){
_start:
{
uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_res_2427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2424_, v_a_2425_, v_x_2426_);
lean_dec(v_x_2426_);
lean_dec_ref(v_a_2425_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2429_, lean_object* v_data_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2432_, lean_object* v_a_2433_, lean_object* v_b_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2433_, v_b_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2437_, lean_object* v_lo_2438_, lean_object* v_hi_2439_, lean_object* v_hhi_2440_, lean_object* v_pivot_2441_, lean_object* v_as_2442_, lean_object* v_i_2443_, lean_object* v_k_2444_, lean_object* v_ilo_2445_, lean_object* v_ik_2446_, lean_object* v_w_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2439_, v_pivot_2441_, v_as_2442_, v_i_2443_, v_k_2444_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2449_, lean_object* v_lo_2450_, lean_object* v_hi_2451_, lean_object* v_hhi_2452_, lean_object* v_pivot_2453_, lean_object* v_as_2454_, lean_object* v_i_2455_, lean_object* v_k_2456_, lean_object* v_ilo_2457_, lean_object* v_ik_2458_, lean_object* v_w_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2449_, v_lo_2450_, v_hi_2451_, v_hhi_2452_, v_pivot_2453_, v_as_2454_, v_i_2455_, v_k_2456_, v_ilo_2457_, v_ik_2458_, v_w_2459_);
lean_dec_ref(v_pivot_2453_);
lean_dec(v_hi_2451_);
lean_dec(v_lo_2450_);
lean_dec(v_n_2449_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2461_, lean_object* v_i_2462_, lean_object* v_source_2463_, lean_object* v_target_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2462_, v_source_2463_, v_target_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2466_, lean_object* v_i_2467_, lean_object* v_source_2468_, lean_object* v_target_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2467_, v_source_2468_, v_target_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2472_, v_x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2475_, lean_object* v_x_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2476_, v_x_2477_);
return v___x_2478_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark);
l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark = _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
}
#ifdef __cplusplus
}
#endif
