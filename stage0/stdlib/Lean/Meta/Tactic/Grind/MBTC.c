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
lean_object* v_ref_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_564_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 5);
v___x_519_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_564_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_564_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_564_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v_traceState_525_; lean_object* v_env_526_; lean_object* v_nextMacroScope_527_; lean_object* v_ngen_528_; lean_object* v_auxDeclNGen_529_; lean_object* v_cache_530_; lean_object* v_messages_531_; lean_object* v_infoState_532_; lean_object* v_snapshotTasks_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_563_; 
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
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_563_ == 0)
{
v___x_535_ = v___x_524_;
v_isShared_536_ = v_isSharedCheck_563_;
goto v_resetjp_534_;
}
else
{
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
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_563_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint64_t v_tid_537_; lean_object* v_traces_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_562_; 
v_tid_537_ = lean_ctor_get_uint64(v_traceState_525_, sizeof(void*)*1);
v_traces_538_ = lean_ctor_get(v_traceState_525_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_traceState_525_);
if (v_isSharedCheck_562_ == 0)
{
v___x_540_ = v_traceState_525_;
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_traces_538_);
lean_dec(v_traceState_525_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; double v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_542_ = lean_box(0);
v___x_543_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_544_ = 0;
v___x_545_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_546_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_546_, 0, v_cls_511_);
lean_ctor_set(v___x_546_, 1, v___x_542_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
lean_ctor_set_float(v___x_546_, sizeof(void*)*3, v___x_543_);
lean_ctor_set_float(v___x_546_, sizeof(void*)*3 + 8, v___x_543_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*3 + 16, v___x_544_);
v___x_547_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_548_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v_a_520_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
lean_inc(v_ref_518_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_ref_518_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_Lean_PersistentArray_push___redArg(v_traces_538_, v___x_549_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_550_);
v___x_552_ = v___x_540_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_550_);
lean_ctor_set_uint64(v_reuseFailAlloc_561_, sizeof(void*)*1, v_tid_537_);
v___x_552_ = v_reuseFailAlloc_561_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 4, v___x_552_);
v___x_554_ = v___x_535_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_env_526_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_nextMacroScope_527_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_ngen_528_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_auxDeclNGen_529_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_cache_530_);
lean_ctor_set(v_reuseFailAlloc_560_, 6, v_messages_531_);
lean_ctor_set(v_reuseFailAlloc_560_, 7, v_infoState_532_);
lean_ctor_set(v_reuseFailAlloc_560_, 8, v_snapshotTasks_533_);
v___x_554_ = v_reuseFailAlloc_560_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_st_ref_set(v___y_516_, v___x_554_);
v___x_556_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_556_);
v___x_558_ = v___x_522_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_565_, lean_object* v_msg_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_565_, v_msg_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
uint8_t v___x_575_; 
v___x_575_ = 0;
return v___x_575_;
}
else
{
lean_object* v_key_576_; lean_object* v_tail_577_; uint8_t v___x_578_; 
v_key_576_ = lean_ctor_get(v_x_574_, 0);
v_tail_577_ = lean_ctor_get(v_x_574_, 2);
v___x_578_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_576_, v_a_573_);
if (v___x_578_ == 0)
{
v_x_574_ = v_tail_577_;
goto _start;
}
else
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_a_580_, lean_object* v_x_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec_ref(v_a_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
return v_x_584_;
}
else
{
lean_object* v_key_586_; lean_object* v_value_587_; lean_object* v_tail_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_611_; 
v_key_586_ = lean_ctor_get(v_x_585_, 0);
v_value_587_ = lean_ctor_get(v_x_585_, 1);
v_tail_588_ = lean_ctor_get(v_x_585_, 2);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_611_ == 0)
{
v___x_590_ = v_x_585_;
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_tail_588_);
lean_inc(v_value_587_);
lean_inc(v_key_586_);
lean_dec(v_x_585_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v_fold_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_592_ = lean_array_get_size(v_x_584_);
v___x_593_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_586_);
v___x_594_ = 32ULL;
v___x_595_ = lean_uint64_shift_right(v___x_593_, v___x_594_);
v_fold_596_ = lean_uint64_xor(v___x_593_, v___x_595_);
v___x_597_ = 16ULL;
v___x_598_ = lean_uint64_shift_right(v_fold_596_, v___x_597_);
v___x_599_ = lean_uint64_xor(v_fold_596_, v___x_598_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = lean_usize_of_nat(v___x_592_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_sub(v___x_601_, v___x_602_);
v___x_604_ = lean_usize_land(v___x_600_, v___x_603_);
v___x_605_ = lean_array_uget_borrowed(v_x_584_, v___x_604_);
lean_inc(v___x_605_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 2, v___x_605_);
v___x_607_ = v___x_590_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_key_586_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_value_587_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v___x_605_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_uset(v_x_584_, v___x_604_, v___x_607_);
v_x_584_ = v___x_608_;
v_x_585_ = v_tail_588_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object* v_i_612_, lean_object* v_source_613_, lean_object* v_target_614_){
_start:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_array_get_size(v_source_613_);
v___x_616_ = lean_nat_dec_lt(v_i_612_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v_source_613_);
lean_dec(v_i_612_);
return v_target_614_;
}
else
{
lean_object* v_es_617_; lean_object* v___x_618_; lean_object* v_source_619_; lean_object* v_target_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_es_617_ = lean_array_fget(v_source_613_, v_i_612_);
v___x_618_ = lean_box(0);
v_source_619_ = lean_array_fset(v_source_613_, v_i_612_, v___x_618_);
v_target_620_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_614_, v_es_617_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_i_612_, v___x_621_);
lean_dec(v_i_612_);
v_i_612_ = v___x_622_;
v_source_613_ = v_source_619_;
v_target_614_ = v_target_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object* v_data_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_nbuckets_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_625_ = lean_array_get_size(v_data_624_);
v___x_626_ = lean_unsigned_to_nat(2u);
v_nbuckets_627_ = lean_nat_mul(v___x_625_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_box(0);
v___x_630_ = lean_mk_array(v_nbuckets_627_, v___x_629_);
v___x_631_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_628_, v_data_624_, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_632_, lean_object* v_a_633_, lean_object* v_b_634_){
_start:
{
lean_object* v_size_635_; lean_object* v_buckets_636_; lean_object* v___x_637_; uint64_t v___x_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v_fold_641_; uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v_bkt_650_; uint8_t v___x_651_; 
v_size_635_ = lean_ctor_get(v_m_632_, 0);
v_buckets_636_ = lean_ctor_get(v_m_632_, 1);
v___x_637_ = lean_array_get_size(v_buckets_636_);
v___x_638_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_633_);
v___x_639_ = 32ULL;
v___x_640_ = lean_uint64_shift_right(v___x_638_, v___x_639_);
v_fold_641_ = lean_uint64_xor(v___x_638_, v___x_640_);
v___x_642_ = 16ULL;
v___x_643_ = lean_uint64_shift_right(v_fold_641_, v___x_642_);
v___x_644_ = lean_uint64_xor(v_fold_641_, v___x_643_);
v___x_645_ = lean_uint64_to_usize(v___x_644_);
v___x_646_ = lean_usize_of_nat(v___x_637_);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_sub(v___x_646_, v___x_647_);
v___x_649_ = lean_usize_land(v___x_645_, v___x_648_);
v_bkt_650_ = lean_array_uget_borrowed(v_buckets_636_, v___x_649_);
v___x_651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_633_, v_bkt_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_672_; 
lean_inc_ref(v_buckets_636_);
lean_inc(v_size_635_);
v_isSharedCheck_672_ = !lean_is_exclusive(v_m_632_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_673_ = lean_ctor_get(v_m_632_, 1);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_m_632_, 0);
lean_dec(v_unused_674_);
v___x_653_ = v_m_632_;
v_isShared_654_ = v_isSharedCheck_672_;
goto v_resetjp_652_;
}
else
{
lean_dec(v_m_632_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_672_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v_size_x27_656_; lean_object* v___x_657_; lean_object* v_buckets_x27_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_655_ = lean_unsigned_to_nat(1u);
v_size_x27_656_ = lean_nat_add(v_size_635_, v___x_655_);
lean_dec(v_size_635_);
lean_inc(v_bkt_650_);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v_a_633_);
lean_ctor_set(v___x_657_, 1, v_b_634_);
lean_ctor_set(v___x_657_, 2, v_bkt_650_);
v_buckets_x27_658_ = lean_array_uset(v_buckets_636_, v___x_649_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(4u);
v___x_660_ = lean_nat_mul(v_size_x27_656_, v___x_659_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_div(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_array_get_size(v_buckets_x27_658_);
v___x_664_ = lean_nat_dec_le(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
if (v___x_664_ == 0)
{
lean_object* v_val_665_; lean_object* v___x_667_; 
v_val_665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_658_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_val_665_);
lean_ctor_set(v___x_653_, 0, v_size_x27_656_);
v___x_667_ = v___x_653_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_x27_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_val_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_670_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_buckets_x27_658_);
lean_ctor_set(v___x_653_, 0, v_size_x27_656_);
v___x_670_ = v___x_653_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_size_x27_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_buckets_x27_658_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_dec(v_b_634_);
lean_dec_ref(v_a_633_);
return v_m_632_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_ctx_675_, lean_object* v_val_676_, lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v_as_x27_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
if (lean_obj_tag(v_as_x27_679_) == 0)
{
lean_object* v___x_692_; 
lean_dec(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_val_676_);
lean_dec_ref(v_ctx_675_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_b_680_);
return v___x_692_;
}
else
{
lean_object* v_head_693_; lean_object* v_tail_694_; lean_object* v_eqAssignment_695_; lean_object* v_arg_696_; lean_object* v___x_697_; 
v_head_693_ = lean_ctor_get(v_as_x27_679_, 0);
v_tail_694_ = lean_ctor_get(v_as_x27_679_, 1);
v_eqAssignment_695_ = lean_ctor_get(v_ctx_675_, 2);
v_arg_696_ = lean_ctor_get(v_head_693_, 0);
lean_inc_ref(v_eqAssignment_695_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
lean_inc(v___y_684_);
lean_inc_ref(v___y_683_);
lean_inc(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v_arg_696_);
lean_inc_ref(v_val_676_);
v___x_697_ = lean_apply_13(v_eqAssignment_695_, v_val_676_, v_arg_696_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; uint8_t v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
if (v___x_699_ == 0)
{
v_as_x27_679_ = v_tail_694_;
goto _start;
}
else
{
lean_object* v___x_701_; 
lean_inc_ref(v_arg_696_);
lean_inc_ref(v_val_676_);
v___x_701_ = l_Lean_Meta_Grind_hasSameType(v_val_676_, v_arg_696_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v___x_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_701_);
v___x_703_ = lean_unbox(v_a_702_);
lean_dec(v_a_702_);
if (v___x_703_ == 0)
{
v_as_x27_679_ = v_tail_694_;
goto _start;
}
else
{
lean_object* v___x_705_; 
lean_inc(v___x_678_);
lean_inc(v_head_693_);
lean_inc_ref(v___x_677_);
v___x_705_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_677_, v_head_693_, v___x_678_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = lean_box(0);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_680_, v_a_706_, v___x_707_);
v_as_x27_679_ = v_tail_694_;
v_b_680_ = v___x_708_;
goto _start;
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_b_680_);
lean_dec(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_val_676_);
lean_dec_ref(v_ctx_675_);
v_a_710_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_705_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_705_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_b_680_);
lean_dec(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_val_676_);
lean_dec_ref(v_ctx_675_);
v_a_718_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_701_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_701_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_b_680_);
lean_dec(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_val_676_);
lean_dec_ref(v_ctx_675_);
v_a_726_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_697_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_697_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_ctx_734_ = _args[0];
lean_object* v_val_735_ = _args[1];
lean_object* v___x_736_ = _args[2];
lean_object* v___x_737_ = _args[3];
lean_object* v_as_x27_738_ = _args[4];
lean_object* v_b_739_ = _args[5];
lean_object* v___y_740_ = _args[6];
lean_object* v___y_741_ = _args[7];
lean_object* v___y_742_ = _args[8];
lean_object* v___y_743_ = _args[9];
lean_object* v___y_744_ = _args[10];
lean_object* v___y_745_ = _args[11];
lean_object* v___y_746_ = _args[12];
lean_object* v___y_747_ = _args[13];
lean_object* v___y_748_ = _args[14];
lean_object* v___y_749_ = _args[15];
lean_object* v___y_750_ = _args[16];
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_734_, v_val_735_, v___x_736_, v___x_737_, v_as_x27_738_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v_as_x27_738_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* v_a_752_, lean_object* v_b_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_dec(v_b_753_);
lean_dec_ref(v_a_752_);
return v_x_754_;
}
else
{
lean_object* v_key_755_; lean_object* v_value_756_; lean_object* v_tail_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_769_; 
v_key_755_ = lean_ctor_get(v_x_754_, 0);
v_value_756_ = lean_ctor_get(v_x_754_, 1);
v_tail_757_ = lean_ctor_get(v_x_754_, 2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_754_);
if (v_isSharedCheck_769_ == 0)
{
v___x_759_ = v_x_754_;
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_tail_757_);
lean_inc(v_value_756_);
lean_inc(v_key_755_);
lean_dec(v_x_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
uint8_t v___x_761_; 
v___x_761_ = lean_expr_eqv(v_key_755_, v_a_752_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_752_, v_b_753_, v_tail_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v___x_762_);
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_key_755_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_value_756_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_767_; 
lean_dec(v_value_756_);
lean_dec(v_key_755_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v_b_753_);
lean_ctor_set(v___x_759_, 0, v_a_752_);
v___x_767_ = v___x_759_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_b_753_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_tail_757_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
uint8_t v___x_772_; 
v___x_772_ = 0;
return v___x_772_;
}
else
{
lean_object* v_key_773_; lean_object* v_tail_774_; uint8_t v___x_775_; 
v_key_773_ = lean_ctor_get(v_x_771_, 0);
v_tail_774_ = lean_ctor_get(v_x_771_, 2);
v___x_775_ = lean_expr_eqv(v_key_773_, v_a_770_);
if (v___x_775_ == 0)
{
v_x_771_ = v_tail_774_;
goto _start;
}
else
{
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* v_a_777_, lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_777_, v_x_778_);
lean_dec(v_x_778_);
lean_dec_ref(v_a_777_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
return v_x_781_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_808_; 
v_key_783_ = lean_ctor_get(v_x_782_, 0);
v_value_784_ = lean_ctor_get(v_x_782_, 1);
v_tail_785_ = lean_ctor_get(v_x_782_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_808_ == 0)
{
v___x_787_ = v_x_782_;
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_tail_785_);
lean_inc(v_value_784_);
lean_inc(v_key_783_);
lean_dec(v_x_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v_fold_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_789_ = lean_array_get_size(v_x_781_);
v___x_790_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_783_);
v___x_791_ = 32ULL;
v___x_792_ = lean_uint64_shift_right(v___x_790_, v___x_791_);
v_fold_793_ = lean_uint64_xor(v___x_790_, v___x_792_);
v___x_794_ = 16ULL;
v___x_795_ = lean_uint64_shift_right(v_fold_793_, v___x_794_);
v___x_796_ = lean_uint64_xor(v_fold_793_, v___x_795_);
v___x_797_ = lean_uint64_to_usize(v___x_796_);
v___x_798_ = lean_usize_of_nat(v___x_789_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_sub(v___x_798_, v___x_799_);
v___x_801_ = lean_usize_land(v___x_797_, v___x_800_);
v___x_802_ = lean_array_uget_borrowed(v_x_781_, v___x_801_);
lean_inc(v___x_802_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_802_);
v___x_804_ = v___x_787_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_key_783_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_value_784_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___x_802_);
v___x_804_ = v_reuseFailAlloc_807_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; 
v___x_805_ = lean_array_uset(v_x_781_, v___x_801_, v___x_804_);
v_x_781_ = v___x_805_;
v_x_782_ = v_tail_785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* v_i_809_, lean_object* v_source_810_, lean_object* v_target_811_){
_start:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_array_get_size(v_source_810_);
v___x_813_ = lean_nat_dec_lt(v_i_809_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec_ref(v_source_810_);
lean_dec(v_i_809_);
return v_target_811_;
}
else
{
lean_object* v_es_814_; lean_object* v___x_815_; lean_object* v_source_816_; lean_object* v_target_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_es_814_ = lean_array_fget(v_source_810_, v_i_809_);
v___x_815_ = lean_box(0);
v_source_816_ = lean_array_fset(v_source_810_, v_i_809_, v___x_815_);
v_target_817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_811_, v_es_814_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_i_809_, v___x_818_);
lean_dec(v_i_809_);
v_i_809_ = v___x_819_;
v_source_810_ = v_source_816_;
v_target_811_ = v_target_817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* v_data_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_nbuckets_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_822_ = lean_array_get_size(v_data_821_);
v___x_823_ = lean_unsigned_to_nat(2u);
v_nbuckets_824_ = lean_nat_mul(v___x_822_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_box(0);
v___x_827_ = lean_mk_array(v_nbuckets_824_, v___x_826_);
v___x_828_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_825_, v_data_821_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_829_, lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_size_832_; lean_object* v_buckets_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_876_; 
v_size_832_ = lean_ctor_get(v_m_829_, 0);
v_buckets_833_ = lean_ctor_get(v_m_829_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_m_829_);
if (v_isSharedCheck_876_ == 0)
{
v___x_835_ = v_m_829_;
v_isShared_836_ = v_isSharedCheck_876_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_buckets_833_);
lean_inc(v_size_832_);
lean_dec(v_m_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_876_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint64_t v___x_838_; uint64_t v___x_839_; uint64_t v___x_840_; uint64_t v_fold_841_; uint64_t v___x_842_; uint64_t v___x_843_; uint64_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; lean_object* v_bkt_850_; uint8_t v___x_851_; 
v___x_837_ = lean_array_get_size(v_buckets_833_);
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_830_);
v___x_839_ = 32ULL;
v___x_840_ = lean_uint64_shift_right(v___x_838_, v___x_839_);
v_fold_841_ = lean_uint64_xor(v___x_838_, v___x_840_);
v___x_842_ = 16ULL;
v___x_843_ = lean_uint64_shift_right(v_fold_841_, v___x_842_);
v___x_844_ = lean_uint64_xor(v_fold_841_, v___x_843_);
v___x_845_ = lean_uint64_to_usize(v___x_844_);
v___x_846_ = lean_usize_of_nat(v___x_837_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_sub(v___x_846_, v___x_847_);
v___x_849_ = lean_usize_land(v___x_845_, v___x_848_);
v_bkt_850_ = lean_array_uget_borrowed(v_buckets_833_, v___x_849_);
v___x_851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_830_, v_bkt_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v_size_x27_853_; lean_object* v___x_854_; lean_object* v_buckets_x27_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_852_ = lean_unsigned_to_nat(1u);
v_size_x27_853_ = lean_nat_add(v_size_832_, v___x_852_);
lean_dec(v_size_832_);
lean_inc(v_bkt_850_);
v___x_854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_854_, 0, v_a_830_);
lean_ctor_set(v___x_854_, 1, v_b_831_);
lean_ctor_set(v___x_854_, 2, v_bkt_850_);
v_buckets_x27_855_ = lean_array_uset(v_buckets_833_, v___x_849_, v___x_854_);
v___x_856_ = lean_unsigned_to_nat(4u);
v___x_857_ = lean_nat_mul(v_size_x27_853_, v___x_856_);
v___x_858_ = lean_unsigned_to_nat(3u);
v___x_859_ = lean_nat_div(v___x_857_, v___x_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_array_get_size(v_buckets_x27_855_);
v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_860_);
lean_dec(v___x_859_);
if (v___x_861_ == 0)
{
lean_object* v_val_862_; lean_object* v___x_864_; 
v_val_862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_855_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_val_862_);
lean_ctor_set(v___x_835_, 0, v_size_x27_853_);
v___x_864_ = v___x_835_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_size_x27_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_val_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_buckets_x27_855_);
lean_ctor_set(v___x_835_, 0, v_size_x27_853_);
v___x_867_ = v___x_835_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_size_x27_853_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_buckets_x27_855_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v___x_869_; lean_object* v_buckets_x27_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_inc(v_bkt_850_);
v___x_869_ = lean_box(0);
v_buckets_x27_870_ = lean_array_uset(v_buckets_833_, v___x_849_, v___x_869_);
v___x_871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_830_, v_b_831_, v_bkt_850_);
v___x_872_ = lean_array_uset(v_buckets_x27_870_, v___x_849_, v___x_871_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_872_);
v___x_874_ = v___x_835_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_size_832_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v_arg_882_; uint8_t v___x_883_; 
v_head_880_ = lean_ctor_get(v_x_878_, 0);
v_tail_881_ = lean_ctor_get(v_x_878_, 1);
v_arg_882_ = lean_ctor_get(v_head_880_, 0);
v___x_883_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_877_, v_arg_882_);
if (v___x_883_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_885_, lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec_ref(v_val_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_901_ = l_Lean_Name_append(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_908_, lean_object* v_ctx_909_, lean_object* v___x_910_, lean_object* v_as_911_, size_t v_sz_912_, size_t v_i_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_a_927_; uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_913_, v_sz_912_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v___x_910_);
lean_dec_ref(v_ctx_909_);
lean_dec_ref(v_e_908_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_b_914_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v_snd_934_; lean_object* v_fst_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_1045_; 
v___x_933_ = lean_st_ref_get(v___y_915_);
v_snd_934_ = lean_ctor_get(v_b_914_, 1);
v_fst_935_ = lean_ctor_get(v_b_914_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_b_914_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_937_ = v_b_914_;
v_isShared_938_ = v_isSharedCheck_1045_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_934_);
lean_inc(v_fst_935_);
lean_dec(v_b_914_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_1045_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1044_; 
v_fst_939_ = lean_ctor_get(v_snd_934_, 0);
v_snd_940_ = lean_ctor_get(v_snd_934_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_934_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_942_ = v_snd_934_;
v_isShared_943_ = v_isSharedCheck_1044_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_939_);
lean_dec(v_snd_934_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1044_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_map_945_; lean_object* v_candidates_946_; lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_array_uget_borrowed(v_as_911_, v_i_913_);
v___x_956_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_933_, v_a_955_);
lean_dec(v___x_933_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1041_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_1041_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1041_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_hasTheoryVar_1001_; lean_object* v___x_1002_; 
v_hasTheoryVar_1001_ = lean_ctor_get(v_ctx_909_, 1);
lean_inc_ref(v_hasTheoryVar_1001_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc(v___y_915_);
lean_inc(v_val_957_);
v___x_1002_ = lean_apply_12(v_hasTheoryVar_1001_, v_val_957_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; uint8_t v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_unbox(v_a_1003_);
lean_dec(v_a_1003_);
if (v___x_1004_ == 0)
{
lean_del_object(v___x_959_);
lean_dec(v_val_957_);
v_map_945_ = v_fst_935_;
v_candidates_946_ = v_fst_939_;
goto v___jp_944_;
}
else
{
lean_object* v_options_1005_; uint8_t v_hasTrace_1006_; 
v_options_1005_ = lean_ctor_get(v___y_923_, 2);
v_hasTrace_1006_ = lean_ctor_get_uint8(v_options_1005_, sizeof(void*)*1);
if (v_hasTrace_1006_ == 0)
{
lean_del_object(v___x_959_);
v___y_962_ = v___y_915_;
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
goto v___jp_961_;
}
else
{
lean_object* v_inheritedTraceOptions_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_inheritedTraceOptions_1007_ = lean_ctor_get(v___y_923_, 13);
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1007_, v_options_1005_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_del_object(v___x_959_);
v___y_962_ = v___y_915_;
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_val_957_);
v___x_1011_ = l_Lean_MessageData_ofExpr(v_val_957_);
v___x_1012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_inc_ref(v___x_910_);
v___x_1014_ = l_Lean_MessageData_ofExpr(v___x_910_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
lean_inc(v_snd_940_);
v___x_1018_ = l_Nat_reprFast(v_snd_940_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 3);
lean_ctor_set(v___x_959_, 0, v___x_1018_);
v___x_1020_ = v___x_959_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_MessageData_ofFormat(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1017_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1008_, v___x_1022_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref(v___x_1023_);
v___y_962_ = v___y_915_;
v___y_963_ = v___y_916_;
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
goto v___jp_961_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_val_957_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec(v_fst_939_);
lean_del_object(v___x_937_);
lean_dec(v_fst_935_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v_ctx_909_);
lean_dec_ref(v_e_908_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
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
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_del_object(v___x_959_);
lean_dec(v_val_957_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec(v_fst_939_);
lean_del_object(v___x_937_);
lean_dec(v_fst_935_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v_ctx_909_);
lean_dec_ref(v_e_908_);
v_a_1033_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1002_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1002_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
v___jp_961_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc_ref_n(v_e_908_, 2);
lean_inc(v_val_957_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_val_957_);
lean_ctor_set(v___x_972_, 1, v_e_908_);
v___x_973_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_908_, v_snd_940_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_935_, v_a_974_);
if (lean_obj_tag(v___x_975_) == 1)
{
lean_object* v_val_976_; uint8_t v___x_977_; 
v_val_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_957_, v_val_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_inc(v_snd_940_);
lean_inc_ref(v___x_972_);
lean_inc_ref(v_ctx_909_);
v___x_978_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_909_, v_val_957_, v___x_972_, v_snd_940_, v_val_976_, v_fst_939_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_972_);
lean_ctor_set(v___x_980_, 1, v_val_976_);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_935_, v_a_974_, v___x_980_);
v_map_945_ = v___x_981_;
v_candidates_946_ = v_a_979_;
goto v___jp_944_;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_val_976_);
lean_dec(v_a_974_);
lean_dec_ref(v___x_972_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_del_object(v___x_937_);
lean_dec(v_fst_935_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v_ctx_909_);
lean_dec_ref(v_e_908_);
v_a_982_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_978_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_978_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_dec(v_val_976_);
lean_dec(v_a_974_);
lean_dec_ref(v___x_972_);
lean_dec(v_val_957_);
v_map_945_ = v_fst_935_;
v_candidates_946_ = v_fst_939_;
goto v___jp_944_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v___x_975_);
lean_dec(v_val_957_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_972_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_935_, v_a_974_, v___x_991_);
v_map_945_ = v___x_992_;
v_candidates_946_ = v_fst_939_;
goto v___jp_944_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v___x_972_);
lean_dec(v_val_957_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec(v_fst_939_);
lean_del_object(v___x_937_);
lean_dec(v_fst_935_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v_ctx_909_);
lean_dec_ref(v_e_908_);
v_a_993_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_973_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_973_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v___x_956_);
lean_del_object(v___x_942_);
lean_del_object(v___x_937_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_fst_939_);
lean_ctor_set(v___x_1042_, 1, v_snd_940_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_fst_935_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v_a_927_ = v___x_1043_;
goto v___jp_926_;
}
v___jp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_snd_940_, v___x_947_);
lean_dec(v_snd_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_948_);
lean_ctor_set(v___x_942_, 0, v_candidates_946_);
v___x_950_ = v___x_942_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_candidates_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_950_);
lean_ctor_set(v___x_937_, 0, v_map_945_);
v___x_952_ = v___x_937_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_map_945_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
v_a_927_ = v___x_952_;
goto v___jp_926_;
}
}
}
}
}
}
v___jp_926_:
{
size_t v___x_928_; size_t v___x_929_; 
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_913_, v___x_928_);
v_i_913_ = v___x_929_;
v_b_914_ = v_a_927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1046_ = _args[0];
lean_object* v_ctx_1047_ = _args[1];
lean_object* v___x_1048_ = _args[2];
lean_object* v_as_1049_ = _args[3];
lean_object* v_sz_1050_ = _args[4];
lean_object* v_i_1051_ = _args[5];
lean_object* v_b_1052_ = _args[6];
lean_object* v___y_1053_ = _args[7];
lean_object* v___y_1054_ = _args[8];
lean_object* v___y_1055_ = _args[9];
lean_object* v___y_1056_ = _args[10];
lean_object* v___y_1057_ = _args[11];
lean_object* v___y_1058_ = _args[12];
lean_object* v___y_1059_ = _args[13];
lean_object* v___y_1060_ = _args[14];
lean_object* v___y_1061_ = _args[15];
lean_object* v___y_1062_ = _args[16];
lean_object* v___y_1063_ = _args[17];
_start:
{
size_t v_sz_boxed_1064_; size_t v_i_boxed_1065_; lean_object* v_res_1066_; 
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1050_);
lean_dec(v_sz_1050_);
v_i_boxed_1065_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1046_, v_ctx_1047_, v___x_1048_, v_as_1049_, v_sz_boxed_1064_, v_i_boxed_1065_, v_b_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v_as_1049_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1067_, lean_object* v_as_1068_, size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref(v_ctx_1067_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_b_1071_);
return v___x_1084_;
}
else
{
lean_object* v_snd_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1186_; 
v_snd_1085_ = lean_ctor_get(v_b_1071_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_b_1071_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_b_1071_, 0);
lean_dec(v_unused_1187_);
v___x_1087_ = v_b_1071_;
v_isShared_1088_ = v_isSharedCheck_1186_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1085_);
lean_dec(v_b_1071_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1186_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_fst_1089_; lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1185_; 
v_fst_1089_ = lean_ctor_get(v_snd_1085_, 0);
v_snd_1090_ = lean_ctor_get(v_snd_1085_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_snd_1085_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1092_ = v_snd_1085_;
v_isShared_1093_ = v_isSharedCheck_1185_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_inc(v_fst_1089_);
lean_dec(v_snd_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1185_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v_a_1096_; lean_object* v_a_1109_; uint8_t v___y_1111_; uint8_t v___x_1183_; 
v___x_1094_ = lean_box(0);
v_a_1109_ = lean_array_uget_borrowed(v_as_1068_, v_i_1070_);
v___x_1183_ = l_Lean_Expr_isApp(v_a_1109_);
if (v___x_1183_ == 0)
{
v___y_1111_ = v___x_1183_;
goto v___jp_1110_;
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = l_Lean_Expr_isEq(v_a_1109_);
if (v___x_1184_ == 0)
{
v___y_1111_ = v___x_1183_;
goto v___jp_1110_;
}
else
{
goto v___jp_1103_;
}
}
v___jp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v_a_1096_);
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_a_1096_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
size_t v___x_1099_; size_t v___x_1100_; 
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1070_, v___x_1099_);
v_i_1070_ = v___x_1100_;
v_b_1071_ = v___x_1098_;
goto _start;
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v_snd_1090_);
lean_ctor_set(v___x_1087_, 0, v_fst_1089_);
v___x_1105_ = v___x_1087_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_fst_1089_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_snd_1090_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v_a_1096_ = v___x_1105_;
goto v___jp_1095_;
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_fst_1089_);
lean_ctor_set(v___x_1108_, 1, v_snd_1090_);
v_a_1096_ = v___x_1108_;
goto v___jp_1095_;
}
v___jp_1110_:
{
if (v___y_1111_ == 0)
{
goto v___jp_1103_;
}
else
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Expr_isHEq(v_a_1109_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_del_object(v___x_1087_);
lean_inc(v_a_1109_);
v___x_1113_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1109_, v___y_1072_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; uint8_t v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = lean_unbox(v_a_1114_);
lean_dec(v_a_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_fst_1089_);
lean_ctor_set(v___x_1116_, 1, v_snd_1090_);
v_a_1096_ = v___x_1116_;
goto v___jp_1095_;
}
else
{
lean_object* v_isInterpreted_1117_; lean_object* v___x_1118_; 
v_isInterpreted_1117_ = lean_ctor_get(v_ctx_1067_, 0);
lean_inc_ref(v_isInterpreted_1117_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc(v_a_1109_);
v___x_1118_ = lean_apply_12(v_isInterpreted_1117_, v_a_1109_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l_Lean_Expr_getAppFn(v_a_1109_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1121_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; uint8_t v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = lean_unbox(v_a_1123_);
lean_dec(v_a_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1121_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v_dummy_1127_; lean_object* v_nargs_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; size_t v_sz_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v_dummy_1127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1128_ = l_Lean_Expr_getAppNumArgs(v_a_1109_);
lean_inc(v_nargs_1128_);
v___x_1129_ = lean_mk_array(v_nargs_1128_, v_dummy_1127_);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_sub(v_nargs_1128_, v___x_1130_);
lean_dec(v_nargs_1128_);
lean_inc_n(v_a_1109_, 2);
v___x_1132_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1109_, v___x_1129_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_snd_1090_);
lean_ctor_set(v___x_1133_, 1, v___x_1126_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_fst_1089_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v_sz_1135_ = lean_array_size(v___x_1132_);
v___x_1136_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1067_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1109_, v_ctx_1067_, v___x_1121_, v___x_1132_, v_sz_1135_, v___x_1136_, v___x_1134_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec_ref(v___x_1132_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v_snd_1139_; lean_object* v_fst_1140_; lean_object* v_fst_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref(v___x_1137_);
v_snd_1139_ = lean_ctor_get(v_a_1138_, 1);
lean_inc(v_snd_1139_);
v_fst_1140_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_fst_1140_);
lean_dec(v_a_1138_);
v_fst_1141_ = lean_ctor_get(v_snd_1139_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_snd_1139_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_snd_1139_, 1);
lean_dec(v_unused_1149_);
v___x_1143_ = v_snd_1139_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_fst_1141_);
lean_dec(v_snd_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_fst_1141_);
lean_ctor_set(v___x_1143_, 0, v_fst_1140_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_fst_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v_a_1096_ = v___x_1146_;
goto v___jp_1095_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_del_object(v___x_1092_);
lean_dec_ref(v_ctx_1067_);
v_a_1150_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1137_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1137_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_dec_ref(v___x_1121_);
goto v___jp_1107_;
}
}
else
{
lean_dec_ref(v___x_1121_);
goto v___jp_1107_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___x_1121_);
lean_del_object(v___x_1092_);
lean_dec(v_snd_1090_);
lean_dec(v_fst_1089_);
lean_dec_ref(v_ctx_1067_);
v_a_1158_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1122_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1122_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_fst_1089_);
lean_ctor_set(v___x_1166_, 1, v_snd_1090_);
v_a_1096_ = v___x_1166_;
goto v___jp_1095_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_del_object(v___x_1092_);
lean_dec(v_snd_1090_);
lean_dec(v_fst_1089_);
lean_dec_ref(v_ctx_1067_);
v_a_1167_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1118_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1118_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_del_object(v___x_1092_);
lean_dec(v_snd_1090_);
lean_dec(v_fst_1089_);
lean_dec_ref(v_ctx_1067_);
v_a_1175_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1113_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1113_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
goto v___jp_1103_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object* v_ctx_1188_, lean_object* v_as_1189_, lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
size_t v_sz_boxed_1204_; size_t v_i_boxed_1205_; lean_object* v_res_1206_; 
v_sz_boxed_1204_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1205_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1188_, v_as_1189_, v_sz_boxed_1204_, v_i_boxed_1205_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v_as_1189_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1207_, lean_object* v_as_1208_, size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_ctx_1207_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_b_1211_);
return v___x_1224_;
}
else
{
lean_object* v_snd_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1326_; 
v_snd_1225_ = lean_ctor_get(v_b_1211_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_b_1211_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_b_1211_, 0);
lean_dec(v_unused_1327_);
v___x_1227_ = v_b_1211_;
v_isShared_1228_ = v_isSharedCheck_1326_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_snd_1225_);
lean_dec(v_b_1211_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1326_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1325_; 
v_fst_1229_ = lean_ctor_get(v_snd_1225_, 0);
v_snd_1230_ = lean_ctor_get(v_snd_1225_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_snd_1225_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1232_ = v_snd_1225_;
v_isShared_1233_ = v_isSharedCheck_1325_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_snd_1225_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1325_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v_a_1236_; lean_object* v_a_1249_; uint8_t v___y_1251_; uint8_t v___x_1323_; 
v___x_1234_ = lean_box(0);
v_a_1249_ = lean_array_uget_borrowed(v_as_1208_, v_i_1210_);
v___x_1323_ = l_Lean_Expr_isApp(v_a_1249_);
if (v___x_1323_ == 0)
{
v___y_1251_ = v___x_1323_;
goto v___jp_1250_;
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_Expr_isEq(v_a_1249_);
if (v___x_1324_ == 0)
{
v___y_1251_ = v___x_1323_;
goto v___jp_1250_;
}
else
{
goto v___jp_1243_;
}
}
v___jp_1235_:
{
lean_object* v___x_1238_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_a_1236_);
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1238_ = v___x_1232_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_a_1236_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_add(v_i_1210_, v___x_1239_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1207_, v_as_1208_, v_sz_1209_, v___x_1240_, v___x_1238_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
return v___x_1241_;
}
}
v___jp_1243_:
{
lean_object* v___x_1245_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_snd_1230_);
lean_ctor_set(v___x_1227_, 0, v_fst_1229_);
v___x_1245_ = v___x_1227_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fst_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_snd_1230_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
v_a_1236_ = v___x_1245_;
goto v___jp_1235_;
}
}
v___jp_1247_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_fst_1229_);
lean_ctor_set(v___x_1248_, 1, v_snd_1230_);
v_a_1236_ = v___x_1248_;
goto v___jp_1235_;
}
v___jp_1250_:
{
if (v___y_1251_ == 0)
{
goto v___jp_1243_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_Expr_isHEq(v_a_1249_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_del_object(v___x_1227_);
lean_inc(v_a_1249_);
v___x_1253_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1249_, v___y_1212_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; uint8_t v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_fst_1229_);
lean_ctor_set(v___x_1256_, 1, v_snd_1230_);
v_a_1236_ = v___x_1256_;
goto v___jp_1235_;
}
else
{
lean_object* v_isInterpreted_1257_; lean_object* v___x_1258_; 
v_isInterpreted_1257_ = lean_ctor_get(v_ctx_1207_, 0);
lean_inc_ref(v_isInterpreted_1257_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
lean_inc(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc(v_a_1249_);
v___x_1258_ = lean_apply_12(v_isInterpreted_1257_, v_a_1249_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, lean_box(0));
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; uint8_t v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = lean_unbox(v_a_1259_);
lean_dec(v_a_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = l_Lean_Expr_getAppFn(v_a_1249_);
lean_inc_ref(v___x_1261_);
v___x_1262_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1261_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; uint8_t v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = lean_unbox(v_a_1263_);
lean_dec(v_a_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1261_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v_dummy_1267_; lean_object* v_nargs_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; size_t v_sz_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
v_dummy_1267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1268_ = l_Lean_Expr_getAppNumArgs(v_a_1249_);
lean_inc(v_nargs_1268_);
v___x_1269_ = lean_mk_array(v_nargs_1268_, v_dummy_1267_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_sub(v_nargs_1268_, v___x_1270_);
lean_dec(v_nargs_1268_);
lean_inc_n(v_a_1249_, 2);
v___x_1272_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1249_, v___x_1269_, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_snd_1230_);
lean_ctor_set(v___x_1273_, 1, v___x_1266_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_fst_1229_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v_sz_1275_ = lean_array_size(v___x_1272_);
v___x_1276_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1207_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1249_, v_ctx_1207_, v___x_1261_, v___x_1272_, v_sz_1275_, v___x_1276_, v___x_1274_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec_ref(v___x_1272_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v_snd_1279_; lean_object* v_fst_1280_; lean_object* v_fst_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v_snd_1279_ = lean_ctor_get(v_a_1278_, 1);
lean_inc(v_snd_1279_);
v_fst_1280_ = lean_ctor_get(v_a_1278_, 0);
lean_inc(v_fst_1280_);
lean_dec(v_a_1278_);
v_fst_1281_ = lean_ctor_get(v_snd_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_snd_1279_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_snd_1279_, 1);
lean_dec(v_unused_1289_);
v___x_1283_ = v_snd_1279_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_fst_1281_);
lean_dec(v_snd_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v_fst_1281_);
lean_ctor_set(v___x_1283_, 0, v_fst_1280_);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1280_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_fst_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v_a_1236_ = v___x_1286_;
goto v___jp_1235_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1232_);
lean_dec_ref(v_ctx_1207_);
v_a_1290_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1277_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1277_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_dec_ref(v___x_1261_);
goto v___jp_1247_;
}
}
else
{
lean_dec_ref(v___x_1261_);
goto v___jp_1247_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v___x_1261_);
lean_del_object(v___x_1232_);
lean_dec(v_snd_1230_);
lean_dec(v_fst_1229_);
lean_dec_ref(v_ctx_1207_);
v_a_1298_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1262_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1262_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_fst_1229_);
lean_ctor_set(v___x_1306_, 1, v_snd_1230_);
v_a_1236_ = v___x_1306_;
goto v___jp_1235_;
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_del_object(v___x_1232_);
lean_dec(v_snd_1230_);
lean_dec(v_fst_1229_);
lean_dec_ref(v_ctx_1207_);
v_a_1307_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1258_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1258_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_del_object(v___x_1232_);
lean_dec(v_snd_1230_);
lean_dec(v_fst_1229_);
lean_dec_ref(v_ctx_1207_);
v_a_1315_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1253_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1253_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
goto v___jp_1243_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object* v_ctx_1328_, lean_object* v_as_1329_, lean_object* v_sz_1330_, lean_object* v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1330_);
lean_dec(v_sz_1330_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1331_);
lean_dec(v_i_1331_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1328_, v_as_1329_, v_sz_boxed_1344_, v_i_boxed_1345_, v_b_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v_as_1329_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref(v_ctx_1347_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1351_);
return v___x_1364_;
}
else
{
lean_object* v_snd_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1466_; 
v_snd_1365_ = lean_ctor_get(v_b_1351_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_b_1351_, 0);
lean_dec(v_unused_1467_);
v___x_1367_ = v_b_1351_;
v_isShared_1368_ = v_isSharedCheck_1466_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1365_);
lean_dec(v_b_1351_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1466_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1465_; 
v_fst_1369_ = lean_ctor_get(v_snd_1365_, 0);
v_snd_1370_ = lean_ctor_get(v_snd_1365_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_snd_1365_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1372_ = v_snd_1365_;
v_isShared_1373_ = v_isSharedCheck_1465_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snd_1370_);
lean_inc(v_fst_1369_);
lean_dec(v_snd_1365_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1465_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v_a_1376_; lean_object* v_a_1389_; uint8_t v___y_1391_; uint8_t v___x_1463_; 
v___x_1374_ = lean_box(0);
v_a_1389_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v___x_1463_ = l_Lean_Expr_isApp(v_a_1389_);
if (v___x_1463_ == 0)
{
v___y_1391_ = v___x_1463_;
goto v___jp_1390_;
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = l_Lean_Expr_isEq(v_a_1389_);
if (v___x_1464_ == 0)
{
v___y_1391_ = v___x_1463_;
goto v___jp_1390_;
}
else
{
goto v___jp_1383_;
}
}
v___jp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_a_1376_);
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1378_ = v___x_1372_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_a_1376_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
size_t v___x_1379_; size_t v___x_1380_; 
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1350_, v___x_1379_);
v_i_1350_ = v___x_1380_;
v_b_1351_ = v___x_1378_;
goto _start;
}
}
v___jp_1383_:
{
lean_object* v___x_1385_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_snd_1370_);
lean_ctor_set(v___x_1367_, 0, v_fst_1369_);
v___x_1385_ = v___x_1367_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_fst_1369_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1370_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v_a_1376_ = v___x_1385_;
goto v___jp_1375_;
}
}
v___jp_1387_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_fst_1369_);
lean_ctor_set(v___x_1388_, 1, v_snd_1370_);
v_a_1376_ = v___x_1388_;
goto v___jp_1375_;
}
v___jp_1390_:
{
if (v___y_1391_ == 0)
{
goto v___jp_1383_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Expr_isHEq(v_a_1389_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1367_);
lean_inc(v_a_1389_);
v___x_1393_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1389_, v___y_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; uint8_t v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_unbox(v_a_1394_);
lean_dec(v_a_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_fst_1369_);
lean_ctor_set(v___x_1396_, 1, v_snd_1370_);
v_a_1376_ = v___x_1396_;
goto v___jp_1375_;
}
else
{
lean_object* v_isInterpreted_1397_; lean_object* v___x_1398_; 
v_isInterpreted_1397_ = lean_ctor_get(v_ctx_1347_, 0);
lean_inc_ref(v_isInterpreted_1397_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
lean_inc(v_a_1389_);
v___x_1398_ = lean_apply_12(v_isInterpreted_1397_, v_a_1389_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, lean_box(0));
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = lean_unbox(v_a_1399_);
lean_dec(v_a_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = l_Lean_Expr_getAppFn(v_a_1389_);
lean_inc_ref(v___x_1401_);
v___x_1402_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1401_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; uint8_t v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1401_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v_dummy_1407_; lean_object* v_nargs_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v_dummy_1407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1408_ = l_Lean_Expr_getAppNumArgs(v_a_1389_);
lean_inc(v_nargs_1408_);
v___x_1409_ = lean_mk_array(v_nargs_1408_, v_dummy_1407_);
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_sub(v_nargs_1408_, v___x_1410_);
lean_dec(v_nargs_1408_);
lean_inc_n(v_a_1389_, 2);
v___x_1412_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1389_, v___x_1409_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_snd_1370_);
lean_ctor_set(v___x_1413_, 1, v___x_1406_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_fst_1369_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v_sz_1415_ = lean_array_size(v___x_1412_);
v___x_1416_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1347_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1389_, v_ctx_1347_, v___x_1401_, v___x_1412_, v_sz_1415_, v___x_1416_, v___x_1414_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec_ref(v___x_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v_snd_1419_; lean_object* v_fst_1420_; lean_object* v_fst_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v_snd_1419_ = lean_ctor_get(v_a_1418_, 1);
lean_inc(v_snd_1419_);
v_fst_1420_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_fst_1420_);
lean_dec(v_a_1418_);
v_fst_1421_ = lean_ctor_get(v_snd_1419_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_snd_1419_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_snd_1419_, 1);
lean_dec(v_unused_1429_);
v___x_1423_ = v_snd_1419_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_fst_1421_);
lean_dec(v_snd_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_fst_1421_);
lean_ctor_set(v___x_1423_, 0, v_fst_1420_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1420_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_fst_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
v_a_1376_ = v___x_1426_;
goto v___jp_1375_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1372_);
lean_dec_ref(v_ctx_1347_);
v_a_1430_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1417_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_dec_ref(v___x_1401_);
goto v___jp_1387_;
}
}
else
{
lean_dec_ref(v___x_1401_);
goto v___jp_1387_;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___x_1401_);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v_fst_1369_);
lean_dec_ref(v_ctx_1347_);
v_a_1438_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1402_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1402_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_fst_1369_);
lean_ctor_set(v___x_1446_, 1, v_snd_1370_);
v_a_1376_ = v___x_1446_;
goto v___jp_1375_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v_fst_1369_);
lean_dec_ref(v_ctx_1347_);
v_a_1447_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1398_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1398_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v_fst_1369_);
lean_dec_ref(v_ctx_1347_);
v_a_1455_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1393_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1393_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
goto v___jp_1383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object* v_ctx_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1468_, v_as_1469_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1487_, lean_object* v_as_1488_, size_t v_sz_1489_, size_t v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_usize_dec_lt(v_i_1490_, v_sz_1489_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_ctx_1487_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_b_1491_);
return v___x_1504_;
}
else
{
lean_object* v_snd_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1606_; 
v_snd_1505_ = lean_ctor_get(v_b_1491_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_b_1491_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_b_1491_, 0);
lean_dec(v_unused_1607_);
v___x_1507_ = v_b_1491_;
v_isShared_1508_ = v_isSharedCheck_1606_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snd_1505_);
lean_dec(v_b_1491_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1606_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_fst_1509_; lean_object* v_snd_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1605_; 
v_fst_1509_ = lean_ctor_get(v_snd_1505_, 0);
v_snd_1510_ = lean_ctor_get(v_snd_1505_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_snd_1505_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1512_ = v_snd_1505_;
v_isShared_1513_ = v_isSharedCheck_1605_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_snd_1510_);
lean_inc(v_fst_1509_);
lean_dec(v_snd_1505_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1605_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v_a_1516_; lean_object* v_a_1529_; uint8_t v___y_1531_; uint8_t v___x_1603_; 
v___x_1514_ = lean_box(0);
v_a_1529_ = lean_array_uget_borrowed(v_as_1488_, v_i_1490_);
v___x_1603_ = l_Lean_Expr_isApp(v_a_1529_);
if (v___x_1603_ == 0)
{
v___y_1531_ = v___x_1603_;
goto v___jp_1530_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Expr_isEq(v_a_1529_);
if (v___x_1604_ == 0)
{
v___y_1531_ = v___x_1603_;
goto v___jp_1530_;
}
else
{
goto v___jp_1523_;
}
}
v___jp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v_a_1516_);
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1518_ = v___x_1512_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1490_, v___x_1519_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1487_, v_as_1488_, v_sz_1489_, v___x_1520_, v___x_1518_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1521_;
}
}
v___jp_1523_:
{
lean_object* v___x_1525_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_snd_1510_);
lean_ctor_set(v___x_1507_, 0, v_fst_1509_);
v___x_1525_ = v___x_1507_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_fst_1509_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_snd_1510_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v_a_1516_ = v___x_1525_;
goto v___jp_1515_;
}
}
v___jp_1527_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_fst_1509_);
lean_ctor_set(v___x_1528_, 1, v_snd_1510_);
v_a_1516_ = v___x_1528_;
goto v___jp_1515_;
}
v___jp_1530_:
{
if (v___y_1531_ == 0)
{
goto v___jp_1523_;
}
else
{
uint8_t v___x_1532_; 
v___x_1532_ = l_Lean_Expr_isHEq(v_a_1529_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_del_object(v___x_1507_);
lean_inc(v_a_1529_);
v___x_1533_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1529_, v___y_1492_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; uint8_t v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_fst_1509_);
lean_ctor_set(v___x_1536_, 1, v_snd_1510_);
v_a_1516_ = v___x_1536_;
goto v___jp_1515_;
}
else
{
lean_object* v_isInterpreted_1537_; lean_object* v___x_1538_; 
v_isInterpreted_1537_ = lean_ctor_get(v_ctx_1487_, 0);
lean_inc_ref(v_isInterpreted_1537_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc(v_a_1529_);
v___x_1538_ = lean_apply_12(v_isInterpreted_1537_, v_a_1529_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; uint8_t v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l_Lean_Expr_getAppFn(v_a_1529_);
lean_inc_ref(v___x_1541_);
v___x_1542_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1541_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1541_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v_dummy_1547_; lean_object* v_nargs_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; size_t v_sz_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v_dummy_1547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1548_ = l_Lean_Expr_getAppNumArgs(v_a_1529_);
lean_inc(v_nargs_1548_);
v___x_1549_ = lean_mk_array(v_nargs_1548_, v_dummy_1547_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_sub(v_nargs_1548_, v___x_1550_);
lean_dec(v_nargs_1548_);
lean_inc_n(v_a_1529_, 2);
v___x_1552_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1529_, v___x_1549_, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_snd_1510_);
lean_ctor_set(v___x_1553_, 1, v___x_1546_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_fst_1509_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v_sz_1555_ = lean_array_size(v___x_1552_);
v___x_1556_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1487_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1529_, v_ctx_1487_, v___x_1541_, v___x_1552_, v_sz_1555_, v___x_1556_, v___x_1554_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v_snd_1559_; lean_object* v_fst_1560_; lean_object* v_fst_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v_snd_1559_ = lean_ctor_get(v_a_1558_, 1);
lean_inc(v_snd_1559_);
v_fst_1560_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_fst_1560_);
lean_dec(v_a_1558_);
v_fst_1561_ = lean_ctor_get(v_snd_1559_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_snd_1559_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_snd_1559_, 1);
lean_dec(v_unused_1569_);
v___x_1563_ = v_snd_1559_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_fst_1561_);
lean_dec(v_snd_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v_fst_1561_);
lean_ctor_set(v___x_1563_, 0, v_fst_1560_);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_fst_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v_a_1516_ = v___x_1566_;
goto v___jp_1515_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_del_object(v___x_1512_);
lean_dec_ref(v_ctx_1487_);
v_a_1570_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1557_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1557_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_dec_ref(v___x_1541_);
goto v___jp_1527_;
}
}
else
{
lean_dec_ref(v___x_1541_);
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1541_);
lean_del_object(v___x_1512_);
lean_dec(v_snd_1510_);
lean_dec(v_fst_1509_);
lean_dec_ref(v_ctx_1487_);
v_a_1578_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1542_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1542_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_fst_1509_);
lean_ctor_set(v___x_1586_, 1, v_snd_1510_);
v_a_1516_ = v___x_1586_;
goto v___jp_1515_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_del_object(v___x_1512_);
lean_dec(v_snd_1510_);
lean_dec(v_fst_1509_);
lean_dec_ref(v_ctx_1487_);
v_a_1587_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1538_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1538_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_del_object(v___x_1512_);
lean_dec(v_snd_1510_);
lean_dec(v_fst_1509_);
lean_dec_ref(v_ctx_1487_);
v_a_1595_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1533_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1533_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
goto v___jp_1523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object* v_ctx_1608_, lean_object* v_as_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_sz_boxed_1624_; size_t v_i_boxed_1625_; lean_object* v_res_1626_; 
v_sz_boxed_1624_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1625_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1608_, v_as_1609_, v_sz_boxed_1624_, v_i_boxed_1625_, v_b_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v_as_1609_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1627_, lean_object* v_ctx_1628_, lean_object* v_n_1629_, lean_object* v_b_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
if (lean_obj_tag(v_n_1629_) == 0)
{
lean_object* v_cs_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; size_t v_sz_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v_cs_1642_ = lean_ctor_get(v_n_1629_, 0);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_b_1630_);
v_sz_1645_ = lean_array_size(v_cs_1642_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1627_, v_ctx_1628_, v_cs_1642_, v_sz_1645_, v___x_1646_, v___x_1644_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1662_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; 
v_fst_1652_ = lean_ctor_get(v_a_1648_, 0);
if (lean_obj_tag(v_fst_1652_) == 0)
{
lean_object* v_snd_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v_snd_1653_ = lean_ctor_get(v_a_1648_, 1);
lean_inc(v_snd_1653_);
lean_dec(v_a_1648_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_snd_1653_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1654_);
v___x_1656_ = v___x_1650_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
lean_object* v_val_1658_; lean_object* v___x_1660_; 
lean_inc_ref(v_fst_1652_);
lean_dec(v_a_1648_);
v_val_1658_ = lean_ctor_get(v_fst_1652_, 0);
lean_inc(v_val_1658_);
lean_dec_ref(v_fst_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v_val_1658_);
v___x_1660_ = v___x_1650_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_val_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1647_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1647_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_vs_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; size_t v_sz_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v_vs_1671_ = lean_ctor_get(v_n_1629_, 0);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_b_1630_);
v_sz_1674_ = lean_array_size(v_vs_1671_);
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1628_, v_vs_1671_, v_sz_1674_, v___x_1675_, v___x_1673_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1691_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v_fst_1681_; 
v_fst_1681_ = lean_ctor_get(v_a_1677_, 0);
if (lean_obj_tag(v_fst_1681_) == 0)
{
lean_object* v_snd_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v_snd_1682_ = lean_ctor_get(v_a_1677_, 1);
lean_inc(v_snd_1682_);
lean_dec(v_a_1677_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_snd_1682_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1683_);
v___x_1685_ = v___x_1679_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
else
{
lean_object* v_val_1687_; lean_object* v___x_1689_; 
lean_inc_ref(v_fst_1681_);
lean_dec(v_a_1677_);
v_val_1687_ = lean_ctor_get(v_fst_1681_, 0);
lean_inc(v_val_1687_);
lean_dec_ref(v_fst_1681_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v_val_1687_);
v___x_1689_ = v___x_1679_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_val_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1676_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1676_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1700_, lean_object* v_ctx_1701_, lean_object* v_as_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec_ref(v_ctx_1701_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_b_1705_);
return v___x_1718_;
}
else
{
lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1753_; 
v_snd_1719_ = lean_ctor_get(v_b_1705_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_b_1705_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v_b_1705_, 0);
lean_dec(v_unused_1754_);
v___x_1721_ = v_b_1705_;
v_isShared_1722_ = v_isSharedCheck_1753_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_dec(v_b_1705_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1753_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_array_uget_borrowed(v_as_1702_, v_i_1704_);
lean_inc(v_snd_1719_);
lean_inc_ref(v_ctx_1701_);
v___x_1724_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1700_, v_ctx_1701_, v_a_1723_, v_snd_1719_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1744_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1744_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1744_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
if (lean_obj_tag(v_a_1725_) == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec_ref(v_ctx_1701_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1725_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1729_);
v___x_1731_ = v___x_1721_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_snd_1719_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1731_);
v___x_1733_ = v___x_1727_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_del_object(v___x_1727_);
lean_dec(v_snd_1719_);
v_a_1736_ = lean_ctor_get(v_a_1725_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v_a_1725_);
v___x_1737_ = lean_box(0);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_a_1736_);
lean_ctor_set(v___x_1721_, 0, v___x_1737_);
v___x_1739_ = v___x_1721_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_a_1736_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
size_t v___x_1740_; size_t v___x_1741_; 
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1704_, v___x_1740_);
v_i_1704_ = v___x_1741_;
v_b_1705_ = v___x_1739_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_del_object(v___x_1721_);
lean_dec(v_snd_1719_);
lean_dec_ref(v_ctx_1701_);
v_a_1745_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1724_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1724_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1755_ = _args[0];
lean_object* v_ctx_1756_ = _args[1];
lean_object* v_as_1757_ = _args[2];
lean_object* v_sz_1758_ = _args[3];
lean_object* v_i_1759_ = _args[4];
lean_object* v_b_1760_ = _args[5];
lean_object* v___y_1761_ = _args[6];
lean_object* v___y_1762_ = _args[7];
lean_object* v___y_1763_ = _args[8];
lean_object* v___y_1764_ = _args[9];
lean_object* v___y_1765_ = _args[10];
lean_object* v___y_1766_ = _args[11];
lean_object* v___y_1767_ = _args[12];
lean_object* v___y_1768_ = _args[13];
lean_object* v___y_1769_ = _args[14];
lean_object* v___y_1770_ = _args[15];
lean_object* v___y_1771_ = _args[16];
_start:
{
size_t v_sz_boxed_1772_; size_t v_i_boxed_1773_; lean_object* v_res_1774_; 
v_sz_boxed_1772_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1773_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1755_, v_ctx_1756_, v_as_1757_, v_sz_boxed_1772_, v_i_boxed_1773_, v_b_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v_as_1757_);
lean_dec_ref(v_init_1755_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1775_, lean_object* v_ctx_1776_, lean_object* v_n_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1775_, v_ctx_1776_, v_n_1777_, v_b_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_n_1777_);
lean_dec_ref(v_init_1775_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1791_, lean_object* v_t_1792_, lean_object* v_init_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_root_1805_; lean_object* v_tail_1806_; lean_object* v___x_1807_; 
v_root_1805_ = lean_ctor_get(v_t_1792_, 0);
v_tail_1806_ = lean_ctor_get(v_t_1792_, 1);
lean_inc_ref(v_ctx_1791_);
lean_inc_ref(v_init_1793_);
v___x_1807_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1793_, v_ctx_1791_, v_root_1805_, v_init_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec_ref(v_init_1793_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1844_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1844_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1844_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
if (lean_obj_tag(v_a_1808_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; 
lean_dec_ref(v_ctx_1791_);
v_a_1812_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_a_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; size_t v_sz_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1810_);
v_a_1816_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v_a_1808_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_a_1816_);
v_sz_1819_ = lean_array_size(v_tail_1806_);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1791_, v_tail_1806_, v_sz_1819_, v___x_1820_, v___x_1818_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1835_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; 
v_fst_1826_ = lean_ctor_get(v_a_1822_, 0);
if (lean_obj_tag(v_fst_1826_) == 0)
{
lean_object* v_snd_1827_; lean_object* v___x_1829_; 
v_snd_1827_ = lean_ctor_get(v_a_1822_, 1);
lean_inc(v_snd_1827_);
lean_dec(v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_snd_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_snd_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v_val_1831_; lean_object* v___x_1833_; 
lean_inc_ref(v_fst_1826_);
lean_dec(v_a_1822_);
v_val_1831_ = lean_ctor_get(v_fst_1826_, 0);
lean_inc(v_val_1831_);
lean_dec_ref(v_fst_1826_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_val_1831_);
v___x_1833_ = v___x_1824_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_val_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1821_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1821_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v_ctx_1791_);
v_a_1845_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1807_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1807_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1853_, lean_object* v_t_1854_, lean_object* v_init_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1853_, v_t_1854_, v_init_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_t_1854_);
return v_res_1867_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1873_ = l_Lean_Name_append(v___x_1872_, v___x_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1874_, size_t v_i_1875_, size_t v_stop_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_a_1890_; uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_eq(v_i_1875_, v_stop_1876_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_array_uget_borrowed(v_as_1874_, v_i_1875_);
v___x_1896_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1895_, v___y_1878_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; uint8_t v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1898_ == 0)
{
if (lean_obj_tag(v___x_1895_) == 2)
{
lean_object* v_a_1899_; lean_object* v_b_1900_; lean_object* v_eq_1901_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v_options_1957_; uint8_t v_hasTrace_1958_; 
v_a_1899_ = lean_ctor_get(v___x_1895_, 0);
v_b_1900_ = lean_ctor_get(v___x_1895_, 1);
v_eq_1901_ = lean_ctor_get(v___x_1895_, 3);
v_options_1957_ = lean_ctor_get(v___y_1886_, 2);
v_hasTrace_1958_ = lean_ctor_get_uint8(v_options_1957_, sizeof(void*)*1);
if (v_hasTrace_1958_ == 0)
{
v___y_1926_ = v___y_1878_;
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
goto v___jp_1925_;
}
else
{
lean_object* v_inheritedTraceOptions_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_inheritedTraceOptions_1959_ = lean_ctor_get(v___y_1886_, 13);
v___x_1960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1961_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1959_, v_options_1957_, v___x_1961_);
if (v___x_1962_ == 0)
{
v___y_1926_ = v___y_1878_;
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_inc_ref(v_eq_1901_);
v___x_1963_ = l_Lean_MessageData_ofExpr(v_eq_1901_);
v___x_1964_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1960_, v___x_1963_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_dec_ref(v___x_1964_);
v___y_1926_ = v___y_1878_;
v___y_1927_ = v___y_1879_;
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
goto v___jp_1925_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_b_1877_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
v___jp_1902_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_box(0);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1911_);
lean_inc(v___y_1907_);
lean_inc_ref(v_eq_1901_);
v___x_1915_ = lean_grind_internalize(v_eq_1901_, v___y_1913_, v___x_1914_, v___y_1907_, v___y_1911_, v___y_1905_, v___y_1904_, v___y_1906_, v___y_1903_, v___y_1910_, v___y_1909_, v___y_1908_, v___y_1912_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref(v___x_1915_);
lean_inc_ref(v___x_1895_);
v___x_1916_ = lean_array_push(v_b_1877_, v___x_1895_);
v_a_1890_ = v___x_1916_;
goto v___jp_1889_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v_b_1877_);
v_a_1917_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1915_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1915_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
v___jp_1925_:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1899_, v___y_1926_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1900_, v___y_1926_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v___x_1940_ = lean_nat_dec_le(v_a_1937_, v_a_1939_);
if (v___x_1940_ == 0)
{
lean_dec(v_a_1939_);
v___y_1903_ = v___y_1931_;
v___y_1904_ = v___y_1929_;
v___y_1905_ = v___y_1928_;
v___y_1906_ = v___y_1930_;
v___y_1907_ = v___y_1926_;
v___y_1908_ = v___y_1934_;
v___y_1909_ = v___y_1933_;
v___y_1910_ = v___y_1932_;
v___y_1911_ = v___y_1927_;
v___y_1912_ = v___y_1935_;
v___y_1913_ = v_a_1937_;
goto v___jp_1902_;
}
else
{
lean_dec(v_a_1937_);
v___y_1903_ = v___y_1931_;
v___y_1904_ = v___y_1929_;
v___y_1905_ = v___y_1928_;
v___y_1906_ = v___y_1930_;
v___y_1907_ = v___y_1926_;
v___y_1908_ = v___y_1934_;
v___y_1909_ = v___y_1933_;
v___y_1910_ = v___y_1932_;
v___y_1911_ = v___y_1927_;
v___y_1912_ = v___y_1935_;
v___y_1913_ = v_a_1939_;
goto v___jp_1902_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1937_);
lean_dec_ref(v_b_1877_);
v_a_1941_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1938_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1938_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_b_1877_);
v_a_1949_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1936_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1936_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
v_a_1890_ = v_b_1877_;
goto v___jp_1889_;
}
}
else
{
v_a_1890_ = v_b_1877_;
goto v___jp_1889_;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_b_1877_);
v_a_1973_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1896_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1896_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_b_1877_);
return v___x_1981_;
}
v___jp_1889_:
{
size_t v___x_1891_; size_t v___x_1892_; 
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1875_, v___x_1891_);
v_i_1875_ = v___x_1892_;
v_b_1877_ = v_a_1890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_1982_, lean_object* v_i_1983_, lean_object* v_stop_1984_, lean_object* v_b_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
size_t v_i_boxed_1997_; size_t v_stop_boxed_1998_; lean_object* v_res_1999_; 
v_i_boxed_1997_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_stop_boxed_1998_ = lean_unbox_usize(v_stop_1984_);
lean_dec(v_stop_1984_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_1982_, v_i_boxed_1997_, v_stop_boxed_1998_, v_b_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v_as_1982_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2002_, lean_object* v_start_2003_, lean_object* v_stop_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2017_ = lean_nat_dec_lt(v_start_2003_, v_stop_2004_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2016_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_array_get_size(v_as_2002_);
v___x_2020_ = lean_nat_dec_le(v_stop_2004_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_nat_dec_lt(v_start_2003_, v___x_2019_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2016_);
return v___x_2022_;
}
else
{
size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = lean_usize_of_nat(v_start_2003_);
v___x_2024_ = lean_usize_of_nat(v___x_2019_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2002_, v___x_2023_, v___x_2024_, v___x_2016_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2025_;
}
}
else
{
size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_usize_of_nat(v_start_2003_);
v___x_2027_ = lean_usize_of_nat(v_stop_2004_);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2002_, v___x_2026_, v___x_2027_, v___x_2016_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2029_, lean_object* v_start_2030_, lean_object* v_stop_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2029_, v_start_2030_, v_stop_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec(v_stop_2031_);
lean_dec(v_start_2030_);
lean_dec_ref(v_as_2029_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_mk_array(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2061_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2275_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2275_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2275_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint8_t v_mbtc_2075_; 
v_mbtc_2075_ = lean_ctor_get_uint8(v_a_2071_, sizeof(void*)*12 + 18);
lean_dec(v_a_2071_);
if (v_mbtc_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec_ref(v_ctx_2058_);
v___x_2076_ = lean_box(v_mbtc_2075_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v___x_2080_; 
lean_del_object(v___x_2073_);
v___x_2080_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2059_, v_a_2061_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2274_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2274_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2274_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_unbox(v_a_2081_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v_toGoalState_2087_; lean_object* v_exprs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2083_);
v___x_2086_ = lean_st_ref_get(v_a_2059_);
v_toGoalState_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc_ref(v_toGoalState_2087_);
lean_dec(v___x_2086_);
v_exprs_2088_ = lean_ctor_get(v_toGoalState_2087_, 2);
lean_inc_ref(v_exprs_2088_);
lean_dec_ref(v_toGoalState_2087_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2091_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2058_, v_exprs_2088_, v___x_2090_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec_ref(v_exprs_2088_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2260_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2260_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2260_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_snd_2096_; lean_object* v_size_2097_; lean_object* v_buckets_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2259_; 
v_snd_2096_ = lean_ctor_get(v_a_2092_, 1);
lean_inc(v_snd_2096_);
lean_dec(v_a_2092_);
v_size_2097_ = lean_ctor_get(v_snd_2096_, 0);
v_buckets_2098_ = lean_ctor_get(v_snd_2096_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_snd_2096_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2100_ = v_snd_2096_;
v_isShared_2101_ = v_isSharedCheck_2259_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_buckets_2098_);
lean_inc(v_size_2097_);
lean_dec(v_snd_2096_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2259_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_nat_dec_eq(v_size_2097_, v___x_2089_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_del_object(v___x_2094_);
lean_dec(v_a_2081_);
v___x_2103_ = lean_st_ref_get(v_a_2059_);
v___x_2104_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2061_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___y_2107_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2163_; lean_object* v_toGoalState_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2246_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v_toGoalState_2169_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2103_, 1);
lean_dec(v_unused_2247_);
v___x_2171_ = v___x_2103_;
v_isShared_2172_ = v_isSharedCheck_2246_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_toGoalState_2169_);
lean_dec(v___x_2103_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2246_;
goto v_resetjp_2170_;
}
v___jp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_array_get_size(v___y_2107_);
v___x_2109_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2107_, v___x_2089_, v___x_2108_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec_ref(v___y_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2141_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2141_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2141_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_array_get_size(v_a_2110_);
v___x_2115_ = lean_nat_dec_eq(v___x_2114_, v___x_2089_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; size_t v_sz_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
lean_del_object(v___x_2112_);
v___x_2116_ = lean_box(0);
v_sz_2117_ = lean_array_size(v_a_2110_);
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2110_, v_sz_2117_, v___x_2118_, v___x_2116_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2110_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2128_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_box(v_mbtc_2075_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2123_);
v___x_2125_ = v___x_2121_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2119_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_dec(v_a_2110_);
v___x_2137_ = lean_box(v___x_2102_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2137_);
v___x_2139_ = v___x_2112_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
v_a_2142_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2109_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2109_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2150_:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2153_, v___y_2152_, v___y_2151_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
v___y_2107_ = v___x_2155_;
goto v___jp_2106_;
}
v___jp_2156_:
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_nat_dec_le(v___y_2160_, v___y_2157_);
if (v___x_2161_ == 0)
{
lean_dec(v___y_2157_);
lean_inc(v___y_2160_);
v___y_2151_ = v___y_2160_;
v___y_2152_ = v___y_2158_;
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2160_;
goto v___jp_2150_;
}
else
{
v___y_2151_ = v___y_2160_;
v___y_2152_ = v___y_2158_;
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2157_;
goto v___jp_2150_;
}
}
v___jp_2162_:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_get_size(v___y_2163_);
v___x_2165_ = lean_nat_dec_eq(v___x_2164_, v___x_2089_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_sub(v___x_2164_, v___x_2166_);
v___x_2168_ = lean_nat_dec_le(v___x_2089_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_inc(v___x_2167_);
v___y_2157_ = v___x_2167_;
v___y_2158_ = v___y_2163_;
v___y_2159_ = v___x_2164_;
v___y_2160_ = v___x_2167_;
goto v___jp_2156_;
}
else
{
v___y_2157_ = v___x_2167_;
v___y_2158_ = v___y_2163_;
v___y_2159_ = v___x_2164_;
v___y_2160_ = v___x_2089_;
goto v___jp_2156_;
}
}
else
{
v___y_2107_ = v___y_2163_;
goto v___jp_2106_;
}
}
v_resetjp_2170_:
{
lean_object* v_split_2173_; lean_object* v_splits_2174_; lean_object* v_num_2175_; uint8_t v___x_2176_; 
v_split_2173_ = lean_ctor_get(v_toGoalState_2169_, 14);
lean_inc_ref(v_split_2173_);
lean_dec_ref(v_toGoalState_2169_);
v_splits_2174_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_splits_2174_);
lean_dec(v_a_2105_);
v_num_2175_ = lean_ctor_get(v_split_2173_, 0);
lean_inc(v_num_2175_);
lean_dec_ref(v_split_2173_);
v___x_2176_ = lean_nat_dec_lt(v_splits_2174_, v_num_2175_);
lean_dec(v_num_2175_);
lean_dec(v_splits_2174_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
lean_del_object(v___x_2171_);
lean_del_object(v___x_2100_);
v___x_2177_ = lean_mk_empty_array_with_capacity(v_size_2097_);
lean_dec(v_size_2097_);
v___x_2178_ = lean_array_get_size(v_buckets_2098_);
v___x_2179_ = lean_nat_dec_lt(v___x_2089_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v_buckets_2098_);
v___y_2163_ = v___x_2177_;
goto v___jp_2162_;
}
else
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_nat_dec_le(v___x_2178_, v___x_2178_);
if (v___x_2180_ == 0)
{
if (v___x_2179_ == 0)
{
lean_dec_ref(v_buckets_2098_);
v___y_2163_ = v___x_2177_;
goto v___jp_2162_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = lean_usize_of_nat(v___x_2178_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2098_, v___x_2181_, v___x_2182_, v___x_2177_);
lean_dec_ref(v_buckets_2098_);
v___y_2163_ = v___x_2183_;
goto v___jp_2162_;
}
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_of_nat(v___x_2178_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2098_, v___x_2184_, v___x_2185_, v___x_2177_);
lean_dec_ref(v_buckets_2098_);
v___y_2163_ = v___x_2186_;
goto v___jp_2162_;
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec_ref(v_buckets_2098_);
lean_dec(v_size_2097_);
v___x_2187_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2061_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2229_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2229_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2229_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_unbox(v_a_2190_);
lean_dec(v_a_2190_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_dec(v_a_2188_);
lean_del_object(v___x_2171_);
lean_del_object(v___x_2100_);
v___x_2195_ = lean_box(v___x_2102_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2195_);
v___x_2197_ = v___x_2192_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
else
{
lean_object* v_splits_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_del_object(v___x_2192_);
v_splits_2199_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_splits_2199_);
lean_dec(v_a_2188_);
v___x_2200_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2201_ = l_Nat_reprFast(v_splits_2199_);
v___x_2202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
v___x_2203_ = l_Lean_MessageData_ofFormat(v___x_2202_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 7);
lean_ctor_set(v___x_2171_, 1, v___x_2203_);
lean_ctor_set(v___x_2171_, 0, v___x_2200_);
v___x_2205_ = v___x_2171_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 7);
lean_ctor_set(v___x_2100_, 1, v___x_2206_);
lean_ctor_set(v___x_2100_, 0, v___x_2205_);
v___x_2208_ = v___x_2100_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_Meta_Sym_reportIssue(v___x_2208_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2217_; 
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2209_, 0);
lean_dec(v_unused_2218_);
v___x_2211_ = v___x_2209_;
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v___x_2209_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(v___x_2102_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2209_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2209_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
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
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2188_);
lean_del_object(v___x_2171_);
lean_del_object(v___x_2100_);
v_a_2230_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2189_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2189_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2171_);
lean_del_object(v___x_2100_);
v_a_2238_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2187_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2187_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v___x_2103_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_buckets_2098_);
lean_dec(v_size_2097_);
v_a_2248_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2104_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2104_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v___x_2257_; 
lean_del_object(v___x_2100_);
lean_dec_ref(v_buckets_2098_);
lean_dec(v_size_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_a_2081_);
v___x_2257_ = v___x_2094_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2081_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_a_2081_);
v_a_2261_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2091_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2091_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_ctx_2058_);
v___x_2269_ = 0;
v___x_2270_ = lean_box(v___x_2269_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2270_);
v___x_2272_ = v___x_2083_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2058_);
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_ctx_2058_);
v_a_2276_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2070_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2070_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Meta_Grind_mbtc(v_ctx_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec(v_a_2285_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2297_, lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2297_, v_msg_2298_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2311_, lean_object* v_msg_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2311_, v_msg_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec(v___y_2313_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2325_, lean_object* v_m_2326_, lean_object* v_a_2327_, lean_object* v_b_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2326_, v_a_2327_, v_b_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2330_, lean_object* v_m_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2331_, v_a_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_m_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2334_, v_m_2335_, v_a_2336_);
lean_dec_ref(v_a_2336_);
lean_dec_ref(v_m_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2338_, lean_object* v_val_2339_, lean_object* v___x_2340_, lean_object* v___x_2341_, lean_object* v_as_2342_, lean_object* v_as_x27_2343_, lean_object* v_b_2344_, lean_object* v_a_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2338_, v_val_2339_, v___x_2340_, v___x_2341_, v_as_x27_2343_, v_b_2344_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2358_ = _args[0];
lean_object* v_val_2359_ = _args[1];
lean_object* v___x_2360_ = _args[2];
lean_object* v___x_2361_ = _args[3];
lean_object* v_as_2362_ = _args[4];
lean_object* v_as_x27_2363_ = _args[5];
lean_object* v_b_2364_ = _args[6];
lean_object* v_a_2365_ = _args[7];
lean_object* v___y_2366_ = _args[8];
lean_object* v___y_2367_ = _args[9];
lean_object* v___y_2368_ = _args[10];
lean_object* v___y_2369_ = _args[11];
lean_object* v___y_2370_ = _args[12];
lean_object* v___y_2371_ = _args[13];
lean_object* v___y_2372_ = _args[14];
lean_object* v___y_2373_ = _args[15];
lean_object* v___y_2374_ = _args[16];
lean_object* v___y_2375_ = _args[17];
lean_object* v___y_2376_ = _args[18];
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2358_, v_val_2359_, v___x_2360_, v___x_2361_, v_as_2362_, v_as_x27_2363_, v_b_2364_, v_a_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec(v_as_x27_2363_);
lean_dec(v_as_2362_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2378_, lean_object* v_m_2379_, lean_object* v_a_2380_, lean_object* v_b_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2379_, v_a_2380_, v_b_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2383_, lean_object* v_as_2384_, lean_object* v_lo_2385_, lean_object* v_hi_2386_, lean_object* v_w_2387_, lean_object* v_hlo_2388_, lean_object* v_hhi_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2383_, v_as_2384_, v_lo_2385_, v_hi_2386_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2391_, lean_object* v_as_2392_, lean_object* v_lo_2393_, lean_object* v_hi_2394_, lean_object* v_w_2395_, lean_object* v_hlo_2396_, lean_object* v_hhi_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2391_, v_as_2392_, v_lo_2393_, v_hi_2394_, v_w_2395_, v_hlo_2396_, v_hhi_2397_);
lean_dec(v_hi_2394_);
lean_dec(v_n_2391_);
return v_res_2398_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2399_, lean_object* v_a_2400_, lean_object* v_x_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2400_, v_x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_a_2404_, lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2403_, v_a_2404_, v_x_2405_);
lean_dec(v_x_2405_);
lean_dec_ref(v_a_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2408_, lean_object* v_data_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2411_, lean_object* v_a_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2412_, v_x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2415_, lean_object* v_a_2416_, lean_object* v_x_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2415_, v_a_2416_, v_x_2417_);
lean_dec(v_x_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2419_, lean_object* v_a_2420_, lean_object* v_x_2421_){
_start:
{
uint8_t v___x_2422_; 
v___x_2422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2420_, v_x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2423_, lean_object* v_a_2424_, lean_object* v_x_2425_){
_start:
{
uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_res_2426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2423_, v_a_2424_, v_x_2425_);
lean_dec(v_x_2425_);
lean_dec_ref(v_a_2424_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2428_, lean_object* v_data_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2431_, lean_object* v_a_2432_, lean_object* v_b_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2432_, v_b_2433_, v_x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2436_, lean_object* v_lo_2437_, lean_object* v_hi_2438_, lean_object* v_hhi_2439_, lean_object* v_pivot_2440_, lean_object* v_as_2441_, lean_object* v_i_2442_, lean_object* v_k_2443_, lean_object* v_ilo_2444_, lean_object* v_ik_2445_, lean_object* v_w_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2438_, v_pivot_2440_, v_as_2441_, v_i_2442_, v_k_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2448_, lean_object* v_lo_2449_, lean_object* v_hi_2450_, lean_object* v_hhi_2451_, lean_object* v_pivot_2452_, lean_object* v_as_2453_, lean_object* v_i_2454_, lean_object* v_k_2455_, lean_object* v_ilo_2456_, lean_object* v_ik_2457_, lean_object* v_w_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2448_, v_lo_2449_, v_hi_2450_, v_hhi_2451_, v_pivot_2452_, v_as_2453_, v_i_2454_, v_k_2455_, v_ilo_2456_, v_ik_2457_, v_w_2458_);
lean_dec_ref(v_pivot_2452_);
lean_dec(v_hi_2450_);
lean_dec(v_lo_2449_);
lean_dec(v_n_2448_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2460_, lean_object* v_i_2461_, lean_object* v_source_2462_, lean_object* v_target_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2461_, v_source_2462_, v_target_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2465_, lean_object* v_i_2466_, lean_object* v_source_2467_, lean_object* v_target_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2466_, v_source_2467_, v_target_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2471_, v_x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2474_, lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2475_, v_x_2476_);
return v___x_2477_;
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
