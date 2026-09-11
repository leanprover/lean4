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
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_SplitInfo_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_54_; uint8_t v___x_55_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = lean_unbox(v_a_54_);
lean_dec(v_a_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
v___x_57_ = lean_array_fset(v_b_37_, v_a_36_, v___x_56_);
v_a_44_ = v___x_57_;
goto v___jp_43_;
}
else
{
v_a_44_ = v_b_37_;
goto v___jp_43_;
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_dec_ref(v_b_37_);
lean_dec(v_a_36_);
v_a_58_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_53_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_53_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
v___x_67_ = lean_array_fset(v_b_37_, v_a_36_, v___x_66_);
v_a_44_ = v___x_67_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object* v_upperBound_68_, lean_object* v_i_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_b_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_68_, v_i_69_, v_a_70_, v_a_71_, v_b_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec_ref(v_a_70_);
lean_dec(v_i_69_);
lean_dec(v_upperBound_68_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object* v_i_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
if (lean_obj_tag(v_x_80_) == 5)
{
lean_object* v_fn_88_; lean_object* v_arg_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_fn_88_ = lean_ctor_get(v_x_80_, 0);
lean_inc_ref(v_fn_88_);
v_arg_89_ = lean_ctor_get(v_x_80_, 1);
lean_inc_ref(v_arg_89_);
lean_dec_ref_known(v_x_80_, 2);
v___x_90_ = lean_array_set(v_x_81_, v_x_82_, v_arg_89_);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_sub(v_x_82_, v___x_91_);
lean_dec(v_x_82_);
v_x_80_ = v_fn_88_;
v_x_81_ = v___x_90_;
v_x_82_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_x_82_);
v___x_94_ = lean_box(0);
lean_inc_ref(v_x_80_);
v___x_95_ = l_Lean_Meta_getFunInfo(v_x_80_, v___x_94_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = lean_array_get_size(v_x_81_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v___x_97_, v_i_79_, v_a_96_, v___x_98_, v_x_81_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v_a_96_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_mkAppN(v_x_80_, v_a_100_);
lean_dec(v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_x_80_);
v_a_109_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_99_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_99_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v_x_81_);
lean_dec_ref(v_x_80_);
v_a_117_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_95_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_95_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object* v_i_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_125_, v_x_126_, v_x_127_, v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v_i_125_);
return v_res_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0(void){
_start:
{
lean_object* v___x_135_; lean_object* v_dummy_136_; 
v___x_135_ = lean_box(0);
v_dummy_136_ = l_Lean_Expr_sort___override(v___x_135_);
return v_dummy_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object* v_e_137_, lean_object* v_i_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_dummy_144_; lean_object* v_nargs_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_dummy_144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_145_ = l_Lean_Expr_getAppNumArgs(v_e_137_);
lean_inc(v_nargs_145_);
v___x_146_ = lean_mk_array(v_nargs_145_, v_dummy_144_);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_sub(v_nargs_145_, v___x_147_);
lean_dec(v_nargs_145_);
v___x_149_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_138_, v_e_137_, v___x_146_, v___x_148_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object* v_e_150_, lean_object* v_i_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_150_, v_i_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_i_151_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object* v_upperBound_158_, lean_object* v_i_159_, lean_object* v_a_160_, lean_object* v___x_161_, lean_object* v_inst_162_, lean_object* v_R_163_, lean_object* v_a_164_, lean_object* v_b_165_, lean_object* v_c_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_158_, v_i_159_, v_a_160_, v_a_164_, v_b_165_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object* v_upperBound_173_, lean_object* v_i_174_, lean_object* v_a_175_, lean_object* v___x_176_, lean_object* v_inst_177_, lean_object* v_R_178_, lean_object* v_a_179_, lean_object* v_b_180_, lean_object* v_c_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_173_, v_i_174_, v_a_175_, v___x_176_, v_inst_177_, v_R_178_, v_a_179_, v_b_180_, v_c_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___x_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_i_174_);
lean_dec(v_upperBound_173_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_i_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_arg_198_; lean_object* v_app_199_; lean_object* v_arg_200_; lean_object* v_app_201_; lean_object* v_fst_203_; lean_object* v_snd_204_; uint8_t v___x_244_; 
v_arg_198_ = lean_ctor_get(v_a_188_, 0);
lean_inc_ref(v_arg_198_);
v_app_199_ = lean_ctor_get(v_a_188_, 1);
lean_inc_ref(v_app_199_);
lean_dec_ref(v_a_188_);
v_arg_200_ = lean_ctor_get(v_b_189_, 0);
lean_inc_ref(v_arg_200_);
v_app_201_ = lean_ctor_get(v_b_189_, 1);
lean_inc_ref(v_app_201_);
lean_dec_ref(v_b_189_);
v___x_244_ = lean_expr_lt(v_arg_198_, v_arg_200_);
if (v___x_244_ == 0)
{
v_fst_203_ = v_arg_200_;
v_snd_204_ = v_arg_198_;
goto v___jp_202_;
}
else
{
v_fst_203_ = v_arg_198_;
v_snd_204_ = v_arg_200_;
goto v___jp_202_;
}
v___jp_202_:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_mkEq(v_fst_203_, v_snd_204_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v___x_207_ = l_Lean_Meta_Sym_canon(v_a_206_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = l_Lean_Meta_Sym_shareCommon(v_a_208_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_219_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_219_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_i_190_);
lean_inc_ref(v_app_201_);
lean_inc_ref(v_app_199_);
v___x_214_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_214_, 0, v_app_199_);
lean_ctor_set(v___x_214_, 1, v_app_201_);
lean_ctor_set(v___x_214_, 2, v_i_190_);
v___x_215_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_215_, 0, v_app_199_);
lean_ctor_set(v___x_215_, 1, v_app_201_);
lean_ctor_set(v___x_215_, 2, v_i_190_);
lean_ctor_set(v___x_215_, 3, v_a_210_);
lean_ctor_set(v___x_215_, 4, v___x_214_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_215_);
v___x_217_ = v___x_212_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec_ref(v_app_201_);
lean_dec_ref(v_app_199_);
lean_dec(v_i_190_);
v_a_220_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_209_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_209_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_app_201_);
lean_dec_ref(v_app_199_);
lean_dec(v_i_190_);
v_a_228_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_207_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_207_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v_app_201_);
lean_dec_ref(v_app_199_);
lean_dec(v_i_190_);
v_a_236_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_205_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_205_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg___boxed(lean_object* v_a_245_, lean_object* v_b_246_, lean_object* v_i_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_245_, v_b_246_, v_i_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object* v_a_256_, lean_object* v_b_257_, lean_object* v_i_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_256_, v_b_257_, v_i_258_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object* v_a_271_, lean_object* v_b_272_, lean_object* v_i_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(v_a_271_, v_b_272_, v_i_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec(v_a_274_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object* v_declName_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; lean_object* v_env_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = lean_st_ref_get(v___y_287_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_env_290_);
lean_dec(v___x_289_);
v___x_291_ = l_Lean_isInstanceReducibleCore(v_env_290_, v_declName_286_);
v___x_292_ = lean_box(v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object* v_declName_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_294_, v___y_295_);
lean_dec(v___y_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object* v_declName_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_298_, v___y_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object* v_declName_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object* v_f_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
if (lean_obj_tag(v_f_308_) == 4)
{
lean_object* v_declName_312_; lean_object* v___x_313_; 
v_declName_312_ = lean_ctor_get(v_f_308_, 0);
lean_inc(v_declName_312_);
lean_dec_ref_known(v_f_308_, 2);
v___x_313_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_312_, v_a_310_);
return v___x_313_;
}
else
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v_f_308_);
v___x_314_ = 0;
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object* v_f_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v_f_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* v_as_322_, size_t v_sz_323_, size_t v_i_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_b_325_);
return v___x_338_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_array_uget_borrowed(v_as_322_, v_i_324_);
lean_inc(v_a_339_);
v___x_340_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_339_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; 
lean_dec_ref_known(v___x_340_, 1);
v___x_341_ = lean_box(0);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_324_, v___x_342_);
v_i_324_ = v___x_343_;
v_b_325_ = v___x_341_;
goto _start;
}
else
{
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* v_as_345_, lean_object* v_sz_346_, lean_object* v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
size_t v_sz_boxed_360_; size_t v_i_boxed_361_; lean_object* v_res_362_; 
v_sz_boxed_360_ = lean_unbox_usize(v_sz_346_);
lean_dec(v_sz_346_);
v_i_boxed_361_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_345_, v_sz_boxed_360_, v_i_boxed_361_, v_b_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v_as_345_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
return v_x_363_;
}
else
{
lean_object* v_key_365_; lean_object* v_tail_366_; lean_object* v___x_367_; 
v_key_365_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_key_365_);
v_tail_366_ = lean_ctor_get(v_x_364_, 2);
lean_inc(v_tail_366_);
lean_dec_ref_known(v_x_364_, 3);
v___x_367_ = lean_array_push(v_x_363_, v_key_365_);
v_x_363_ = v___x_367_;
v_x_364_ = v_tail_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object* v_as_369_, size_t v_i_370_, size_t v_stop_371_, lean_object* v_b_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_370_, v_stop_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; 
v___x_374_ = lean_array_uget_borrowed(v_as_369_, v_i_370_);
lean_inc(v___x_374_);
v___x_375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(v_b_372_, v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_370_, v___x_376_);
v_i_370_ = v___x_377_;
v_b_372_ = v___x_375_;
goto _start;
}
else
{
return v_b_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object* v_as_379_, lean_object* v_i_380_, lean_object* v_stop_381_, lean_object* v_b_382_){
_start:
{
size_t v_i_boxed_383_; size_t v_stop_boxed_384_; lean_object* v_res_385_; 
v_i_boxed_383_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_stop_boxed_384_ = lean_unbox_usize(v_stop_381_);
lean_dec(v_stop_381_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_379_, v_i_boxed_383_, v_stop_boxed_384_, v_b_382_);
lean_dec_ref(v_as_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(lean_object* v_hi_386_, lean_object* v_pivot_387_, lean_object* v_as_388_, lean_object* v_i_389_, lean_object* v_k_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_lt(v_k_390_, v_hi_386_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_k_390_);
v___x_392_ = lean_array_fswap(v_as_388_, v_i_389_, v_hi_386_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_i_389_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_fget_borrowed(v_as_388_, v_k_390_);
v___x_395_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_394_, v_pivot_387_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_k_390_, v___x_396_);
lean_dec(v_k_390_);
v_k_390_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_array_fswap(v_as_388_, v_i_389_, v_k_390_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_i_389_, v___x_400_);
lean_dec(v_i_389_);
v___x_402_ = lean_nat_add(v_k_390_, v___x_400_);
lean_dec(v_k_390_);
v_as_388_ = v___x_399_;
v_i_389_ = v___x_401_;
v_k_390_ = v___x_402_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg___boxed(lean_object* v_hi_404_, lean_object* v_pivot_405_, lean_object* v_as_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_404_, v_pivot_405_, v_as_406_, v_i_407_, v_k_408_);
lean_dec_ref(v_pivot_405_);
lean_dec(v_hi_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object* v_n_410_, lean_object* v_as_411_, lean_object* v_lo_412_, lean_object* v_hi_413_){
_start:
{
lean_object* v___y_415_; uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_lt(v_lo_412_, v_hi_413_);
if (v___x_425_ == 0)
{
lean_dec(v_lo_412_);
return v_as_411_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_mid_428_; lean_object* v___y_430_; lean_object* v___y_436_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_426_ = lean_nat_add(v_lo_412_, v_hi_413_);
v___x_427_ = lean_unsigned_to_nat(1u);
v_mid_428_ = lean_nat_shiftr(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_441_ = lean_array_fget_borrowed(v_as_411_, v_mid_428_);
v___x_442_ = lean_array_fget_borrowed(v_as_411_, v_lo_412_);
v___x_443_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_436_ = v_as_411_;
goto v___jp_435_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_array_fswap(v_as_411_, v_lo_412_, v_mid_428_);
v___y_436_ = v___x_444_;
goto v___jp_435_;
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_array_fget_borrowed(v___y_430_, v_mid_428_);
v___x_432_ = lean_array_fget_borrowed(v___y_430_, v_hi_413_);
v___x_433_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_mid_428_);
v___y_415_ = v___y_430_;
goto v___jp_414_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_array_fswap(v___y_430_, v_mid_428_, v_hi_413_);
lean_dec(v_mid_428_);
v___y_415_ = v___x_434_;
goto v___jp_414_;
}
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_array_fget_borrowed(v___y_436_, v_hi_413_);
v___x_438_ = lean_array_fget_borrowed(v___y_436_, v_lo_412_);
v___x_439_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
v___y_430_ = v___y_436_;
goto v___jp_429_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_array_fswap(v___y_436_, v_lo_412_, v_hi_413_);
v___y_430_ = v___x_440_;
goto v___jp_429_;
}
}
}
v___jp_414_:
{
lean_object* v_pivot_416_; lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; uint8_t v___x_420_; 
v_pivot_416_ = lean_array_fget(v___y_415_, v_hi_413_);
lean_inc_n(v_lo_412_, 2);
v___x_417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_413_, v_pivot_416_, v___y_415_, v_lo_412_, v_lo_412_);
lean_dec(v_pivot_416_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_fst_418_);
v_snd_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_snd_419_);
lean_dec_ref(v___x_417_);
v___x_420_ = lean_nat_dec_le(v_hi_413_, v_fst_418_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_410_, v_snd_419_, v_lo_412_, v_fst_418_);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_fst_418_, v___x_422_);
lean_dec(v_fst_418_);
v_as_411_ = v___x_421_;
v_lo_412_ = v___x_423_;
goto _start;
}
else
{
lean_dec(v_fst_418_);
lean_dec(v_lo_412_);
return v_snd_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object* v_n_445_, lean_object* v_as_446_, lean_object* v_lo_447_, lean_object* v_hi_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_445_, v_as_446_, v_lo_447_, v_hi_448_);
lean_dec(v_hi_448_);
lean_dec(v_n_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
lean_object* v_key_453_; lean_object* v_value_454_; lean_object* v_tail_455_; uint8_t v___x_456_; 
v_key_453_ = lean_ctor_get(v_x_451_, 0);
v_value_454_ = lean_ctor_get(v_x_451_, 1);
v_tail_455_ = lean_ctor_get(v_x_451_, 2);
v___x_456_ = lean_expr_eqv(v_key_453_, v_a_450_);
if (v___x_456_ == 0)
{
v_x_451_ = v_tail_455_;
goto _start;
}
else
{
lean_object* v___x_458_; 
lean_inc(v_value_454_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_value_454_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec_ref(v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* v_m_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_buckets_464_; lean_object* v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v_fold_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_buckets_464_ = lean_ctor_get(v_m_462_, 1);
v___x_465_ = lean_array_get_size(v_buckets_464_);
v___x_466_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_463_);
v___x_467_ = 32ULL;
v___x_468_ = lean_uint64_shift_right(v___x_466_, v___x_467_);
v_fold_469_ = lean_uint64_xor(v___x_466_, v___x_468_);
v___x_470_ = 16ULL;
v___x_471_ = lean_uint64_shift_right(v_fold_469_, v___x_470_);
v___x_472_ = lean_uint64_xor(v_fold_469_, v___x_471_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = lean_usize_of_nat(v___x_465_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_land(v___x_473_, v___x_476_);
v___x_478_ = lean_array_uget_borrowed(v_buckets_464_, v___x_477_);
v___x_479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_463_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_480_, v_a_481_);
lean_dec_ref(v_a_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object* v_msgData_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v_env_490_; lean_object* v___x_491_; lean_object* v_toCold_492_; lean_object* v_mctx_493_; lean_object* v_lctx_494_; lean_object* v_options_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_489_ = lean_st_ref_get(v___y_487_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_env_490_);
lean_dec(v___x_489_);
v___x_491_ = lean_st_ref_get(v___y_485_);
v_toCold_492_ = lean_ctor_get(v___y_486_, 0);
v_mctx_493_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_mctx_493_);
lean_dec(v___x_491_);
v_lctx_494_ = lean_ctor_get(v___y_484_, 2);
v_options_495_ = lean_ctor_get(v_toCold_492_, 2);
lean_inc_ref(v_options_495_);
lean_inc_ref(v_lctx_494_);
v___x_496_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_496_, 0, v_env_490_);
lean_ctor_set(v___x_496_, 1, v_mctx_493_);
lean_ctor_set(v___x_496_, 2, v_lctx_494_);
lean_ctor_set(v___x_496_, 3, v_options_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_msgData_483_);
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
v_ref_518_ = lean_ctor_get(v___y_515_, 2);
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
v___x_555_ = lean_st_ref_put(v___y_516_, v___x_554_);
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
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_nbuckets_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_625_ = lean_array_get_size(v_data_624_);
v___x_626_ = lean_unsigned_to_nat(2u);
v_nbuckets_627_ = lean_nat_mul(v___x_625_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_box(0);
v___x_630_ = lean_mk_array(v_nbuckets_627_, v___x_629_);
v___x_631_ = lean_array_propagate_mark(v_data_624_, v___x_630_);
v___x_632_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_628_, v_data_624_, v___x_631_);
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
lean_dec_ref_known(v___x_698_, 1);
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
lean_dec_ref_known(v___x_702_, 1);
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
lean_dec_ref_known(v___x_706_, 1);
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
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_nbuckets_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_823_ = lean_array_get_size(v_data_822_);
v___x_824_ = lean_unsigned_to_nat(2u);
v_nbuckets_825_ = lean_nat_mul(v___x_823_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_box(0);
v___x_828_ = lean_mk_array(v_nbuckets_825_, v___x_827_);
v___x_829_ = lean_array_propagate_mark(v_data_822_, v___x_828_);
v___x_830_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_826_, v_data_822_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_831_, lean_object* v_a_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_size_834_; lean_object* v_buckets_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_878_; 
v_size_834_ = lean_ctor_get(v_m_831_, 0);
v_buckets_835_ = lean_ctor_get(v_m_831_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_m_831_);
if (v_isSharedCheck_878_ == 0)
{
v___x_837_ = v_m_831_;
v_isShared_838_ = v_isSharedCheck_878_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_buckets_835_);
lean_inc(v_size_834_);
lean_dec(v_m_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_878_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v___x_842_; uint64_t v_fold_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; lean_object* v_bkt_852_; uint8_t v___x_853_; 
v___x_839_ = lean_array_get_size(v_buckets_835_);
v___x_840_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_832_);
v___x_841_ = 32ULL;
v___x_842_ = lean_uint64_shift_right(v___x_840_, v___x_841_);
v_fold_843_ = lean_uint64_xor(v___x_840_, v___x_842_);
v___x_844_ = 16ULL;
v___x_845_ = lean_uint64_shift_right(v_fold_843_, v___x_844_);
v___x_846_ = lean_uint64_xor(v_fold_843_, v___x_845_);
v___x_847_ = lean_uint64_to_usize(v___x_846_);
v___x_848_ = lean_usize_of_nat(v___x_839_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_sub(v___x_848_, v___x_849_);
v___x_851_ = lean_usize_land(v___x_847_, v___x_850_);
v_bkt_852_ = lean_array_uget_borrowed(v_buckets_835_, v___x_851_);
v___x_853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_832_, v_bkt_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v_size_x27_855_; lean_object* v___x_856_; lean_object* v_buckets_x27_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v_size_x27_855_ = lean_nat_add(v_size_834_, v___x_854_);
lean_dec(v_size_834_);
lean_inc(v_bkt_852_);
v___x_856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_856_, 0, v_a_832_);
lean_ctor_set(v___x_856_, 1, v_b_833_);
lean_ctor_set(v___x_856_, 2, v_bkt_852_);
v_buckets_x27_857_ = lean_array_uset(v_buckets_835_, v___x_851_, v___x_856_);
v___x_858_ = lean_unsigned_to_nat(4u);
v___x_859_ = lean_nat_mul(v_size_x27_855_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(3u);
v___x_861_ = lean_nat_div(v___x_859_, v___x_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_array_get_size(v_buckets_x27_857_);
v___x_863_ = lean_nat_dec_le(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
if (v___x_863_ == 0)
{
lean_object* v_val_864_; lean_object* v___x_866_; 
v_val_864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_857_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_val_864_);
lean_ctor_set(v___x_837_, 0, v_size_x27_855_);
v___x_866_ = v___x_837_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_size_x27_855_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_val_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
lean_object* v___x_869_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_buckets_x27_857_);
lean_ctor_set(v___x_837_, 0, v_size_x27_855_);
v___x_869_ = v___x_837_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_size_x27_855_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_buckets_x27_857_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v_buckets_x27_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
lean_inc(v_bkt_852_);
v___x_871_ = lean_box(0);
v_buckets_x27_872_ = lean_array_uset(v_buckets_835_, v___x_851_, v___x_871_);
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_832_, v_b_833_, v_bkt_852_);
v___x_874_ = lean_array_uset(v_buckets_x27_872_, v___x_851_, v___x_873_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_874_);
v___x_876_ = v___x_837_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_size_834_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
else
{
lean_object* v_head_882_; lean_object* v_tail_883_; lean_object* v_arg_884_; size_t v___x_885_; size_t v___x_886_; uint8_t v___x_887_; 
v_head_882_ = lean_ctor_get(v_x_880_, 0);
v_tail_883_ = lean_ctor_get(v_x_880_, 1);
v_arg_884_ = lean_ctor_get(v_head_882_, 0);
v___x_885_ = lean_ptr_addr(v_val_879_);
v___x_886_ = lean_ptr_addr(v_arg_884_);
v___x_887_ = lean_usize_dec_eq(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
v_x_880_ = v_tail_883_;
goto _start;
}
else
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_889_, v_x_890_);
lean_dec(v_x_890_);
lean_dec_ref(v_val_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_905_ = l_Lean_Name_append(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_912_, lean_object* v_ctx_913_, lean_object* v___x_914_, lean_object* v_as_915_, size_t v_sz_916_, size_t v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_a_931_; uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_917_, v_sz_916_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_ctx_913_);
lean_dec_ref(v_e_912_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_b_918_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v_snd_938_; lean_object* v_fst_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1050_; 
v___x_937_ = lean_st_ref_get(v___y_919_);
v_snd_938_ = lean_ctor_get(v_b_918_, 1);
v_fst_939_ = lean_ctor_get(v_b_918_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_b_918_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_941_ = v_b_918_;
v_isShared_942_ = v_isSharedCheck_1050_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_938_);
lean_inc(v_fst_939_);
lean_dec(v_b_918_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1050_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1049_; 
v_fst_943_ = lean_ctor_get(v_snd_938_, 0);
v_snd_944_ = lean_ctor_get(v_snd_938_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_snd_938_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_946_ = v_snd_938_;
v_isShared_947_ = v_isSharedCheck_1049_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_inc(v_fst_943_);
lean_dec(v_snd_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1049_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_map_949_; lean_object* v_candidates_950_; lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_array_uget_borrowed(v_as_915_, v_i_917_);
v___x_960_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_937_, v_a_959_);
lean_dec(v___x_937_);
if (lean_obj_tag(v___x_960_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1046_; 
v_val_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_1046_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1046_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v_hasTheoryVar_1005_; lean_object* v___x_1006_; 
v_hasTheoryVar_1005_ = lean_ctor_get(v_ctx_913_, 1);
lean_inc_ref(v_hasTheoryVar_1005_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc(v___y_919_);
lean_inc(v_val_961_);
v___x_1006_ = lean_apply_12(v_hasTheoryVar_1005_, v_val_961_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; uint8_t v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_unbox(v_a_1007_);
lean_dec(v_a_1007_);
if (v___x_1008_ == 0)
{
lean_del_object(v___x_963_);
lean_dec(v_val_961_);
v_map_949_ = v_fst_939_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
else
{
lean_object* v_toCold_1009_; lean_object* v_options_1010_; uint8_t v_hasTrace_1011_; 
v_toCold_1009_ = lean_ctor_get(v___y_927_, 0);
v_options_1010_ = lean_ctor_get(v_toCold_1009_, 2);
v_hasTrace_1011_ = lean_ctor_get_uint8(v_options_1010_, sizeof(void*)*1);
if (v_hasTrace_1011_ == 0)
{
lean_del_object(v___x_963_);
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
goto v___jp_965_;
}
else
{
lean_object* v_inheritedTraceOptions_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_inheritedTraceOptions_1012_ = lean_ctor_get(v_toCold_1009_, 11);
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1012_, v_options_1010_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_del_object(v___x_963_);
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
goto v___jp_965_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_inc(v_val_961_);
v___x_1016_ = l_Lean_MessageData_ofExpr(v_val_961_);
v___x_1017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc_ref(v___x_914_);
v___x_1019_ = l_Lean_MessageData_ofExpr(v___x_914_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_inc(v_snd_944_);
v___x_1023_ = l_Nat_reprFast(v_snd_944_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 3);
lean_ctor_set(v___x_963_, 0, v___x_1023_);
v___x_1025_ = v___x_963_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_MessageData_ofFormat(v___x_1025_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1022_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1013_, v___x_1027_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_dec_ref_known(v___x_1028_, 1);
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
goto v___jp_965_;
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_val_961_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_ctx_913_);
lean_dec_ref(v_e_912_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
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
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_del_object(v___x_963_);
lean_dec(v_val_961_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_ctx_913_);
lean_dec_ref(v_e_912_);
v_a_1038_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1006_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1006_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
v___jp_965_:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc_ref_n(v_e_912_, 2);
lean_inc(v_val_961_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_val_961_);
lean_ctor_set(v___x_976_, 1, v_e_912_);
v___x_977_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_912_, v_snd_944_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_939_, v_a_978_);
if (lean_obj_tag(v___x_979_) == 1)
{
lean_object* v_val_980_; uint8_t v___x_981_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_961_, v_val_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_inc(v_snd_944_);
lean_inc_ref(v___x_976_);
lean_inc_ref(v_ctx_913_);
v___x_982_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_913_, v_val_961_, v___x_976_, v_snd_944_, v_val_980_, v_fst_943_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_976_);
lean_ctor_set(v___x_984_, 1, v_val_980_);
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_939_, v_a_978_, v___x_984_);
v_map_949_ = v___x_985_;
v_candidates_950_ = v_a_983_;
goto v___jp_948_;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_val_980_);
lean_dec(v_a_978_);
lean_dec_ref_known(v___x_976_, 2);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_ctx_913_);
lean_dec_ref(v_e_912_);
v_a_986_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_982_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_dec(v_val_980_);
lean_dec(v_a_978_);
lean_dec_ref_known(v___x_976_, 2);
lean_dec(v_val_961_);
v_map_949_ = v_fst_939_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v___x_979_);
lean_dec(v_val_961_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_976_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_939_, v_a_978_, v___x_995_);
v_map_949_ = v___x_996_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref_known(v___x_976_, 2);
lean_dec(v_val_961_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_ctx_913_);
lean_dec_ref(v_e_912_);
v_a_997_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_977_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_977_);
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
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v___x_960_);
lean_del_object(v___x_946_);
lean_del_object(v___x_941_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_fst_943_);
lean_ctor_set(v___x_1047_, 1, v_snd_944_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_fst_939_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v_a_931_ = v___x_1048_;
goto v___jp_930_;
}
v___jp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_snd_944_, v___x_951_);
lean_dec(v_snd_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_952_);
lean_ctor_set(v___x_946_, 0, v_candidates_950_);
v___x_954_ = v___x_946_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_candidates_950_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_954_);
lean_ctor_set(v___x_941_, 0, v_map_949_);
v___x_956_ = v___x_941_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_map_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v_a_931_ = v___x_956_;
goto v___jp_930_;
}
}
}
}
}
}
v___jp_930_:
{
size_t v___x_932_; size_t v___x_933_; 
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_917_, v___x_932_);
v_i_917_ = v___x_933_;
v_b_918_ = v_a_931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1051_ = _args[0];
lean_object* v_ctx_1052_ = _args[1];
lean_object* v___x_1053_ = _args[2];
lean_object* v_as_1054_ = _args[3];
lean_object* v_sz_1055_ = _args[4];
lean_object* v_i_1056_ = _args[5];
lean_object* v_b_1057_ = _args[6];
lean_object* v___y_1058_ = _args[7];
lean_object* v___y_1059_ = _args[8];
lean_object* v___y_1060_ = _args[9];
lean_object* v___y_1061_ = _args[10];
lean_object* v___y_1062_ = _args[11];
lean_object* v___y_1063_ = _args[12];
lean_object* v___y_1064_ = _args[13];
lean_object* v___y_1065_ = _args[14];
lean_object* v___y_1066_ = _args[15];
lean_object* v___y_1067_ = _args[16];
lean_object* v___y_1068_ = _args[17];
_start:
{
size_t v_sz_boxed_1069_; size_t v_i_boxed_1070_; lean_object* v_res_1071_; 
v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1051_, v_ctx_1052_, v___x_1053_, v_as_1054_, v_sz_boxed_1069_, v_i_boxed_1070_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v_as_1054_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1072_, uint8_t v_a_1073_, lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref(v_ctx_1072_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_b_1077_);
return v___x_1090_;
}
else
{
lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1193_; 
v_snd_1091_ = lean_ctor_get(v_b_1077_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_b_1077_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_b_1077_, 0);
lean_dec(v_unused_1194_);
v___x_1093_ = v_b_1077_;
v_isShared_1094_ = v_isSharedCheck_1193_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_dec(v_b_1077_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1193_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1192_; 
v_fst_1095_ = lean_ctor_get(v_snd_1091_, 0);
v_snd_1096_ = lean_ctor_get(v_snd_1091_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_snd_1091_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1098_ = v_snd_1091_;
v_isShared_1099_ = v_isSharedCheck_1192_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
lean_dec(v_snd_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1192_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v_a_1102_; lean_object* v_a_1115_; uint8_t v___y_1189_; uint8_t v___x_1190_; 
v___x_1100_ = lean_box(0);
v_a_1115_ = lean_array_uget_borrowed(v_as_1074_, v_i_1076_);
v___x_1190_ = l_Lean_Expr_isApp(v_a_1115_);
if (v___x_1190_ == 0)
{
v___y_1189_ = v_a_1073_;
goto v___jp_1188_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_Expr_isEq(v_a_1115_);
if (v___x_1191_ == 0)
{
goto v___jp_1116_;
}
else
{
v___y_1189_ = v_a_1073_;
goto v___jp_1188_;
}
}
v___jp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v_a_1102_);
lean_ctor_set(v___x_1098_, 0, v___x_1100_);
v___x_1104_ = v___x_1098_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_a_1102_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
size_t v___x_1105_; size_t v___x_1106_; 
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_i_1076_, v___x_1105_);
v_i_1076_ = v___x_1106_;
v_b_1077_ = v___x_1104_;
goto _start;
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_snd_1096_);
lean_ctor_set(v___x_1093_, 0, v_fst_1095_);
v___x_1111_ = v___x_1093_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1096_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_a_1102_ = v___x_1111_;
goto v___jp_1101_;
}
}
v___jp_1113_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_fst_1095_);
lean_ctor_set(v___x_1114_, 1, v_snd_1096_);
v_a_1102_ = v___x_1114_;
goto v___jp_1101_;
}
v___jp_1116_:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Lean_Expr_isHEq(v_a_1115_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_inc(v_a_1115_);
v___x_1118_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1115_, v___y_1078_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_del_object(v___x_1093_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_fst_1095_);
lean_ctor_set(v___x_1121_, 1, v_snd_1096_);
v_a_1102_ = v___x_1121_;
goto v___jp_1101_;
}
else
{
lean_object* v_isInterpreted_1122_; lean_object* v___x_1123_; 
v_isInterpreted_1122_ = lean_ctor_get(v_ctx_1072_, 0);
lean_inc_ref(v_isInterpreted_1122_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc(v_a_1115_);
v___x_1123_ = lean_apply_12(v_isInterpreted_1122_, v_a_1115_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, lean_box(0));
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = l_Lean_Expr_getAppFn(v_a_1115_);
lean_inc_ref(v___x_1126_);
v___x_1127_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1126_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; uint8_t v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1126_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v_dummy_1132_; lean_object* v_nargs_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
lean_del_object(v___x_1093_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v_dummy_1132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1133_ = l_Lean_Expr_getAppNumArgs(v_a_1115_);
lean_inc(v_nargs_1133_);
v___x_1134_ = lean_mk_array(v_nargs_1133_, v_dummy_1132_);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_sub(v_nargs_1133_, v___x_1135_);
lean_dec(v_nargs_1133_);
lean_inc_n(v_a_1115_, 2);
v___x_1137_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1115_, v___x_1134_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_snd_1096_);
lean_ctor_set(v___x_1138_, 1, v___x_1131_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_fst_1095_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v_sz_1140_ = lean_array_size(v___x_1137_);
v___x_1141_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1072_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1115_, v_ctx_1072_, v___x_1126_, v___x_1137_, v_sz_1140_, v___x_1141_, v___x_1139_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec_ref(v___x_1137_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_snd_1144_; lean_object* v_fst_1145_; lean_object* v_fst_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v_snd_1144_ = lean_ctor_get(v_a_1143_, 1);
lean_inc(v_snd_1144_);
v_fst_1145_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_fst_1145_);
lean_dec(v_a_1143_);
v_fst_1146_ = lean_ctor_get(v_snd_1144_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_snd_1144_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_snd_1144_, 1);
lean_dec(v_unused_1154_);
v___x_1148_ = v_snd_1144_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_fst_1146_);
lean_dec(v_snd_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_fst_1146_);
lean_ctor_set(v___x_1148_, 0, v_fst_1145_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_fst_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_fst_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
v_a_1102_ = v___x_1151_;
goto v___jp_1101_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_del_object(v___x_1098_);
lean_dec_ref(v_ctx_1072_);
v_a_1155_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1142_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1142_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_dec_ref(v___x_1126_);
goto v___jp_1109_;
}
}
else
{
lean_dec_ref(v___x_1126_);
goto v___jp_1109_;
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___x_1126_);
lean_del_object(v___x_1098_);
lean_dec(v_snd_1096_);
lean_dec(v_fst_1095_);
lean_del_object(v___x_1093_);
lean_dec_ref(v_ctx_1072_);
v_a_1163_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1127_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1127_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v___x_1171_; 
lean_del_object(v___x_1093_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_fst_1095_);
lean_ctor_set(v___x_1171_, 1, v_snd_1096_);
v_a_1102_ = v___x_1171_;
goto v___jp_1101_;
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_del_object(v___x_1098_);
lean_dec(v_snd_1096_);
lean_dec(v_fst_1095_);
lean_del_object(v___x_1093_);
lean_dec_ref(v_ctx_1072_);
v_a_1172_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1123_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1123_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1098_);
lean_dec(v_snd_1096_);
lean_dec(v_fst_1095_);
lean_del_object(v___x_1093_);
lean_dec_ref(v_ctx_1072_);
v_a_1180_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1118_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1118_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_del_object(v___x_1093_);
goto v___jp_1113_;
}
}
v___jp_1188_:
{
if (v___y_1189_ == 0)
{
lean_del_object(v___x_1093_);
goto v___jp_1113_;
}
else
{
goto v___jp_1116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object** _args){
lean_object* v_ctx_1195_ = _args[0];
lean_object* v_a_1196_ = _args[1];
lean_object* v_as_1197_ = _args[2];
lean_object* v_sz_1198_ = _args[3];
lean_object* v_i_1199_ = _args[4];
lean_object* v_b_1200_ = _args[5];
lean_object* v___y_1201_ = _args[6];
lean_object* v___y_1202_ = _args[7];
lean_object* v___y_1203_ = _args[8];
lean_object* v___y_1204_ = _args[9];
lean_object* v___y_1205_ = _args[10];
lean_object* v___y_1206_ = _args[11];
lean_object* v___y_1207_ = _args[12];
lean_object* v___y_1208_ = _args[13];
lean_object* v___y_1209_ = _args[14];
lean_object* v___y_1210_ = _args[15];
lean_object* v___y_1211_ = _args[16];
_start:
{
uint8_t v_a_162242__boxed_1212_; size_t v_sz_boxed_1213_; size_t v_i_boxed_1214_; lean_object* v_res_1215_; 
v_a_162242__boxed_1212_ = lean_unbox(v_a_1196_);
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1198_);
lean_dec(v_sz_1198_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1199_);
lean_dec(v_i_1199_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1195_, v_a_162242__boxed_1212_, v_as_1197_, v_sz_boxed_1213_, v_i_boxed_1214_, v_b_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v_as_1197_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1216_, uint8_t v_a_1217_, lean_object* v_as_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v_ctx_1216_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_b_1221_);
return v___x_1234_;
}
else
{
lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1337_; 
v_snd_1235_ = lean_ctor_get(v_b_1221_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_b_1221_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_b_1221_, 0);
lean_dec(v_unused_1338_);
v___x_1237_ = v_b_1221_;
v_isShared_1238_ = v_isSharedCheck_1337_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_dec(v_b_1221_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1337_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_fst_1239_; lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1336_; 
v_fst_1239_ = lean_ctor_get(v_snd_1235_, 0);
v_snd_1240_ = lean_ctor_get(v_snd_1235_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_snd_1235_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1242_ = v_snd_1235_;
v_isShared_1243_ = v_isSharedCheck_1336_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_inc(v_fst_1239_);
lean_dec(v_snd_1235_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1336_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v_a_1246_; lean_object* v_a_1259_; uint8_t v___y_1333_; uint8_t v___x_1334_; 
v___x_1244_ = lean_box(0);
v_a_1259_ = lean_array_uget_borrowed(v_as_1218_, v_i_1220_);
v___x_1334_ = l_Lean_Expr_isApp(v_a_1259_);
if (v___x_1334_ == 0)
{
v___y_1333_ = v_a_1217_;
goto v___jp_1332_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_Expr_isEq(v_a_1259_);
if (v___x_1335_ == 0)
{
goto v___jp_1260_;
}
else
{
v___y_1333_ = v_a_1217_;
goto v___jp_1332_;
}
}
v___jp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_a_1246_);
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1248_ = v___x_1242_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_a_1246_);
v___x_1248_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
size_t v___x_1249_; size_t v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_i_1220_, v___x_1249_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1216_, v_a_1217_, v_as_1218_, v_sz_1219_, v___x_1250_, v___x_1248_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
return v___x_1251_;
}
}
v___jp_1253_:
{
lean_object* v___x_1255_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_snd_1240_);
lean_ctor_set(v___x_1237_, 0, v_fst_1239_);
v___x_1255_ = v___x_1237_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_fst_1239_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_snd_1240_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v_a_1246_ = v___x_1255_;
goto v___jp_1245_;
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_fst_1239_);
lean_ctor_set(v___x_1258_, 1, v_snd_1240_);
v_a_1246_ = v___x_1258_;
goto v___jp_1245_;
}
v___jp_1260_:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Lean_Expr_isHEq(v_a_1259_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_inc(v_a_1259_);
v___x_1262_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1259_, v___y_1222_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; uint8_t v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_unbox(v_a_1263_);
lean_dec(v_a_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_del_object(v___x_1237_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_fst_1239_);
lean_ctor_set(v___x_1265_, 1, v_snd_1240_);
v_a_1246_ = v___x_1265_;
goto v___jp_1245_;
}
else
{
lean_object* v_isInterpreted_1266_; lean_object* v___x_1267_; 
v_isInterpreted_1266_ = lean_ctor_get(v_ctx_1216_, 0);
lean_inc_ref(v_isInterpreted_1266_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc(v_a_1259_);
v___x_1267_ = lean_apply_12(v_isInterpreted_1266_, v_a_1259_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, lean_box(0));
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = l_Lean_Expr_getAppFn(v_a_1259_);
lean_inc_ref(v___x_1270_);
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1270_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; uint8_t v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1270_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v_dummy_1276_; lean_object* v_nargs_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; size_t v_sz_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
lean_del_object(v___x_1237_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v_dummy_1276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1277_ = l_Lean_Expr_getAppNumArgs(v_a_1259_);
lean_inc(v_nargs_1277_);
v___x_1278_ = lean_mk_array(v_nargs_1277_, v_dummy_1276_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_sub(v_nargs_1277_, v___x_1279_);
lean_dec(v_nargs_1277_);
lean_inc_n(v_a_1259_, 2);
v___x_1281_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1259_, v___x_1278_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_snd_1240_);
lean_ctor_set(v___x_1282_, 1, v___x_1275_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_fst_1239_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v_sz_1284_ = lean_array_size(v___x_1281_);
v___x_1285_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1216_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1259_, v_ctx_1216_, v___x_1270_, v___x_1281_, v_sz_1284_, v___x_1285_, v___x_1283_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec_ref(v___x_1281_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_snd_1288_; lean_object* v_fst_1289_; lean_object* v_fst_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v_snd_1288_ = lean_ctor_get(v_a_1287_, 1);
lean_inc(v_snd_1288_);
v_fst_1289_ = lean_ctor_get(v_a_1287_, 0);
lean_inc(v_fst_1289_);
lean_dec(v_a_1287_);
v_fst_1290_ = lean_ctor_get(v_snd_1288_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_snd_1288_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_snd_1288_, 1);
lean_dec(v_unused_1298_);
v___x_1292_ = v_snd_1288_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_fst_1290_);
lean_dec(v_snd_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v_fst_1290_);
lean_ctor_set(v___x_1292_, 0, v_fst_1289_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_fst_1289_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_fst_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v_a_1246_ = v___x_1295_;
goto v___jp_1245_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_ctx_1216_);
v_a_1299_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1286_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1286_);
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
lean_dec_ref(v___x_1270_);
goto v___jp_1253_;
}
}
else
{
lean_dec_ref(v___x_1270_);
goto v___jp_1253_;
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v___x_1270_);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec_ref(v_ctx_1216_);
v_a_1307_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1271_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1271_);
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
else
{
lean_object* v___x_1315_; 
lean_del_object(v___x_1237_);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_fst_1239_);
lean_ctor_set(v___x_1315_, 1, v_snd_1240_);
v_a_1246_ = v___x_1315_;
goto v___jp_1245_;
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec_ref(v_ctx_1216_);
v_a_1316_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1267_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1267_);
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
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec_ref(v_ctx_1216_);
v_a_1324_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1262_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1262_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_del_object(v___x_1237_);
goto v___jp_1257_;
}
}
v___jp_1332_:
{
if (v___y_1333_ == 0)
{
lean_del_object(v___x_1237_);
goto v___jp_1257_;
}
else
{
goto v___jp_1260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args){
lean_object* v_ctx_1339_ = _args[0];
lean_object* v_a_1340_ = _args[1];
lean_object* v_as_1341_ = _args[2];
lean_object* v_sz_1342_ = _args[3];
lean_object* v_i_1343_ = _args[4];
lean_object* v_b_1344_ = _args[5];
lean_object* v___y_1345_ = _args[6];
lean_object* v___y_1346_ = _args[7];
lean_object* v___y_1347_ = _args[8];
lean_object* v___y_1348_ = _args[9];
lean_object* v___y_1349_ = _args[10];
lean_object* v___y_1350_ = _args[11];
lean_object* v___y_1351_ = _args[12];
lean_object* v___y_1352_ = _args[13];
lean_object* v___y_1353_ = _args[14];
lean_object* v___y_1354_ = _args[15];
lean_object* v___y_1355_ = _args[16];
_start:
{
uint8_t v_a_162470__boxed_1356_; size_t v_sz_boxed_1357_; size_t v_i_boxed_1358_; lean_object* v_res_1359_; 
v_a_162470__boxed_1356_ = lean_unbox(v_a_1340_);
v_sz_boxed_1357_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1358_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1339_, v_a_162470__boxed_1356_, v_as_1341_, v_sz_boxed_1357_, v_i_boxed_1358_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v_as_1341_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1360_, uint8_t v_a_1361_, lean_object* v_as_1362_, size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref(v_ctx_1360_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_b_1365_);
return v___x_1378_;
}
else
{
lean_object* v_snd_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1481_; 
v_snd_1379_ = lean_ctor_get(v_b_1365_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_b_1365_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_b_1365_, 0);
lean_dec(v_unused_1482_);
v___x_1381_ = v_b_1365_;
v_isShared_1382_ = v_isSharedCheck_1481_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snd_1379_);
lean_dec(v_b_1365_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1481_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1480_; 
v_fst_1383_ = lean_ctor_get(v_snd_1379_, 0);
v_snd_1384_ = lean_ctor_get(v_snd_1379_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_snd_1379_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1386_ = v_snd_1379_;
v_isShared_1387_ = v_isSharedCheck_1480_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v_snd_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1480_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v_a_1390_; lean_object* v_a_1403_; uint8_t v___y_1477_; uint8_t v___x_1478_; 
v___x_1388_ = lean_box(0);
v_a_1403_ = lean_array_uget_borrowed(v_as_1362_, v_i_1364_);
v___x_1478_ = l_Lean_Expr_isApp(v_a_1403_);
if (v___x_1478_ == 0)
{
v___y_1477_ = v_a_1361_;
goto v___jp_1476_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Expr_isEq(v_a_1403_);
if (v___x_1479_ == 0)
{
goto v___jp_1404_;
}
else
{
v___y_1477_ = v_a_1361_;
goto v___jp_1476_;
}
}
v___jp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_a_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_a_1390_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
size_t v___x_1393_; size_t v___x_1394_; 
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1364_, v___x_1393_);
v_i_1364_ = v___x_1394_;
v_b_1365_ = v___x_1392_;
goto _start;
}
}
v___jp_1397_:
{
lean_object* v___x_1399_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v_snd_1384_);
lean_ctor_set(v___x_1381_, 0, v_fst_1383_);
v___x_1399_ = v___x_1381_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_fst_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_snd_1384_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v_a_1390_ = v___x_1399_;
goto v___jp_1389_;
}
}
v___jp_1401_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_fst_1383_);
lean_ctor_set(v___x_1402_, 1, v_snd_1384_);
v_a_1390_ = v___x_1402_;
goto v___jp_1389_;
}
v___jp_1404_:
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_Expr_isHEq(v_a_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_inc(v_a_1403_);
v___x_1406_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1403_, v___y_1366_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; uint8_t v___x_1408_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = lean_unbox(v_a_1407_);
lean_dec(v_a_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_del_object(v___x_1381_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_fst_1383_);
lean_ctor_set(v___x_1409_, 1, v_snd_1384_);
v_a_1390_ = v___x_1409_;
goto v___jp_1389_;
}
else
{
lean_object* v_isInterpreted_1410_; lean_object* v___x_1411_; 
v_isInterpreted_1410_ = lean_ctor_get(v_ctx_1360_, 0);
lean_inc_ref(v_isInterpreted_1410_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc(v_a_1403_);
v___x_1411_ = lean_apply_12(v_isInterpreted_1410_, v_a_1403_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, lean_box(0));
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; uint8_t v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = lean_unbox(v_a_1412_);
lean_dec(v_a_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = l_Lean_Expr_getAppFn(v_a_1403_);
lean_inc_ref(v___x_1414_);
v___x_1415_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1414_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; uint8_t v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_unbox(v_a_1416_);
lean_dec(v_a_1416_);
if (v___x_1417_ == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1414_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v_dummy_1420_; lean_object* v_nargs_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; size_t v_sz_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
lean_del_object(v___x_1381_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v_dummy_1420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1421_ = l_Lean_Expr_getAppNumArgs(v_a_1403_);
lean_inc(v_nargs_1421_);
v___x_1422_ = lean_mk_array(v_nargs_1421_, v_dummy_1420_);
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_sub(v_nargs_1421_, v___x_1423_);
lean_dec(v_nargs_1421_);
lean_inc_n(v_a_1403_, 2);
v___x_1425_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1403_, v___x_1422_, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_snd_1384_);
lean_ctor_set(v___x_1426_, 1, v___x_1419_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_fst_1383_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v_sz_1428_ = lean_array_size(v___x_1425_);
v___x_1429_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1360_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1403_, v_ctx_1360_, v___x_1414_, v___x_1425_, v_sz_1428_, v___x_1429_, v___x_1427_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec_ref(v___x_1425_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v_fst_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_snd_1432_ = lean_ctor_get(v_a_1431_, 1);
lean_inc(v_snd_1432_);
v_fst_1433_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_fst_1433_);
lean_dec(v_a_1431_);
v_fst_1434_ = lean_ctor_get(v_snd_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_snd_1432_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_snd_1432_, 1);
lean_dec(v_unused_1442_);
v___x_1436_ = v_snd_1432_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_fst_1434_);
lean_dec(v_snd_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_fst_1434_);
lean_ctor_set(v___x_1436_, 0, v_fst_1433_);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_fst_1433_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_fst_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_a_1390_ = v___x_1439_;
goto v___jp_1389_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_del_object(v___x_1386_);
lean_dec_ref(v_ctx_1360_);
v_a_1443_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1430_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1430_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_dec_ref(v___x_1414_);
goto v___jp_1397_;
}
}
else
{
lean_dec_ref(v___x_1414_);
goto v___jp_1397_;
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec_ref(v_ctx_1360_);
v_a_1451_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1415_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1415_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v___x_1459_; 
lean_del_object(v___x_1381_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_fst_1383_);
lean_ctor_set(v___x_1459_, 1, v_snd_1384_);
v_a_1390_ = v___x_1459_;
goto v___jp_1389_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec_ref(v_ctx_1360_);
v_a_1460_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1411_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1411_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec_ref(v_ctx_1360_);
v_a_1468_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1406_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1406_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_del_object(v___x_1381_);
goto v___jp_1401_;
}
}
v___jp_1476_:
{
if (v___y_1477_ == 0)
{
lean_del_object(v___x_1381_);
goto v___jp_1401_;
}
else
{
goto v___jp_1404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object** _args){
lean_object* v_ctx_1483_ = _args[0];
lean_object* v_a_1484_ = _args[1];
lean_object* v_as_1485_ = _args[2];
lean_object* v_sz_1486_ = _args[3];
lean_object* v_i_1487_ = _args[4];
lean_object* v_b_1488_ = _args[5];
lean_object* v___y_1489_ = _args[6];
lean_object* v___y_1490_ = _args[7];
lean_object* v___y_1491_ = _args[8];
lean_object* v___y_1492_ = _args[9];
lean_object* v___y_1493_ = _args[10];
lean_object* v___y_1494_ = _args[11];
lean_object* v___y_1495_ = _args[12];
lean_object* v___y_1496_ = _args[13];
lean_object* v___y_1497_ = _args[14];
lean_object* v___y_1498_ = _args[15];
lean_object* v___y_1499_ = _args[16];
_start:
{
uint8_t v_a_162698__boxed_1500_; size_t v_sz_boxed_1501_; size_t v_i_boxed_1502_; lean_object* v_res_1503_; 
v_a_162698__boxed_1500_ = lean_unbox(v_a_1484_);
v_sz_boxed_1501_ = lean_unbox_usize(v_sz_1486_);
lean_dec(v_sz_1486_);
v_i_boxed_1502_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_res_1503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1483_, v_a_162698__boxed_1500_, v_as_1485_, v_sz_boxed_1501_, v_i_boxed_1502_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v_as_1485_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1504_, uint8_t v_a_1505_, lean_object* v_as_1506_, size_t v_sz_1507_, size_t v_i_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_lt(v_i_1508_, v_sz_1507_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v_ctx_1504_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_b_1509_);
return v___x_1522_;
}
else
{
lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1625_; 
v_snd_1523_ = lean_ctor_get(v_b_1509_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_b_1509_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v_b_1509_, 0);
lean_dec(v_unused_1626_);
v___x_1525_ = v_b_1509_;
v_isShared_1526_ = v_isSharedCheck_1625_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_dec(v_b_1509_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1625_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1624_; 
v_fst_1527_ = lean_ctor_get(v_snd_1523_, 0);
v_snd_1528_ = lean_ctor_get(v_snd_1523_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_snd_1523_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1530_ = v_snd_1523_;
v_isShared_1531_ = v_isSharedCheck_1624_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v_snd_1523_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1624_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v_a_1534_; lean_object* v_a_1547_; uint8_t v___y_1621_; uint8_t v___x_1622_; 
v___x_1532_ = lean_box(0);
v_a_1547_ = lean_array_uget_borrowed(v_as_1506_, v_i_1508_);
v___x_1622_ = l_Lean_Expr_isApp(v_a_1547_);
if (v___x_1622_ == 0)
{
v___y_1621_ = v_a_1505_;
goto v___jp_1620_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = l_Lean_Expr_isEq(v_a_1547_);
if (v___x_1623_ == 0)
{
goto v___jp_1548_;
}
else
{
v___y_1621_ = v_a_1505_;
goto v___jp_1620_;
}
}
v___jp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_a_1534_);
lean_ctor_set(v___x_1530_, 0, v___x_1532_);
v___x_1536_ = v___x_1530_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_a_1534_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((size_t)1ULL);
v___x_1538_ = lean_usize_add(v_i_1508_, v___x_1537_);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1504_, v_a_1505_, v_as_1506_, v_sz_1507_, v___x_1538_, v___x_1536_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1539_;
}
}
v___jp_1541_:
{
lean_object* v___x_1543_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v_snd_1528_);
lean_ctor_set(v___x_1525_, 0, v_fst_1527_);
v___x_1543_ = v___x_1525_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_fst_1527_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_snd_1528_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
v_a_1534_ = v___x_1543_;
goto v___jp_1533_;
}
}
v___jp_1545_:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_fst_1527_);
lean_ctor_set(v___x_1546_, 1, v_snd_1528_);
v_a_1534_ = v___x_1546_;
goto v___jp_1533_;
}
v___jp_1548_:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lean_Expr_isHEq(v_a_1547_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_a_1547_);
v___x_1550_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1547_, v___y_1510_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; uint8_t v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_del_object(v___x_1525_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_fst_1527_);
lean_ctor_set(v___x_1553_, 1, v_snd_1528_);
v_a_1534_ = v___x_1553_;
goto v___jp_1533_;
}
else
{
lean_object* v_isInterpreted_1554_; lean_object* v___x_1555_; 
v_isInterpreted_1554_ = lean_ctor_get(v_ctx_1504_, 0);
lean_inc_ref(v_isInterpreted_1554_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v___y_1510_);
lean_inc(v_a_1547_);
v___x_1555_ = lean_apply_12(v_isInterpreted_1554_, v_a_1547_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, lean_box(0));
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = lean_unbox(v_a_1556_);
lean_dec(v_a_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = l_Lean_Expr_getAppFn(v_a_1547_);
lean_inc_ref(v___x_1558_);
v___x_1559_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1558_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; uint8_t v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = lean_unbox(v_a_1560_);
lean_dec(v_a_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1558_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v_dummy_1564_; lean_object* v_nargs_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1525_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v_dummy_1564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1565_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
lean_inc(v_nargs_1565_);
v___x_1566_ = lean_mk_array(v_nargs_1565_, v_dummy_1564_);
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_nat_sub(v_nargs_1565_, v___x_1567_);
lean_dec(v_nargs_1565_);
lean_inc_n(v_a_1547_, 2);
v___x_1569_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1547_, v___x_1566_, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_snd_1528_);
lean_ctor_set(v___x_1570_, 1, v___x_1563_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_fst_1527_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v_sz_1572_ = lean_array_size(v___x_1569_);
v___x_1573_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1504_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1547_, v_ctx_1504_, v___x_1558_, v___x_1569_, v_sz_1572_, v___x_1573_, v___x_1571_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec_ref(v___x_1569_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v_snd_1576_; lean_object* v_fst_1577_; lean_object* v_fst_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_snd_1576_ = lean_ctor_get(v_a_1575_, 1);
lean_inc(v_snd_1576_);
v_fst_1577_ = lean_ctor_get(v_a_1575_, 0);
lean_inc(v_fst_1577_);
lean_dec(v_a_1575_);
v_fst_1578_ = lean_ctor_get(v_snd_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_snd_1576_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_snd_1576_, 1);
lean_dec(v_unused_1586_);
v___x_1580_ = v_snd_1576_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_fst_1578_);
lean_dec(v_snd_1576_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_fst_1578_);
lean_ctor_set(v___x_1580_, 0, v_fst_1577_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_fst_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_fst_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v_a_1534_ = v___x_1583_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_del_object(v___x_1530_);
lean_dec_ref(v_ctx_1504_);
v_a_1587_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1574_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1574_);
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
else
{
lean_dec_ref(v___x_1558_);
goto v___jp_1541_;
}
}
else
{
lean_dec_ref(v___x_1558_);
goto v___jp_1541_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v___x_1558_);
lean_del_object(v___x_1530_);
lean_dec(v_snd_1528_);
lean_dec(v_fst_1527_);
lean_del_object(v___x_1525_);
lean_dec_ref(v_ctx_1504_);
v_a_1595_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1559_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1559_);
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
lean_object* v___x_1603_; 
lean_del_object(v___x_1525_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_fst_1527_);
lean_ctor_set(v___x_1603_, 1, v_snd_1528_);
v_a_1534_ = v___x_1603_;
goto v___jp_1533_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1530_);
lean_dec(v_snd_1528_);
lean_dec(v_fst_1527_);
lean_del_object(v___x_1525_);
lean_dec_ref(v_ctx_1504_);
v_a_1604_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1555_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1555_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_del_object(v___x_1530_);
lean_dec(v_snd_1528_);
lean_dec(v_fst_1527_);
lean_del_object(v___x_1525_);
lean_dec_ref(v_ctx_1504_);
v_a_1612_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1550_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1550_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_del_object(v___x_1525_);
goto v___jp_1545_;
}
}
v___jp_1620_:
{
if (v___y_1621_ == 0)
{
lean_del_object(v___x_1525_);
goto v___jp_1545_;
}
else
{
goto v___jp_1548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object** _args){
lean_object* v_ctx_1627_ = _args[0];
lean_object* v_a_1628_ = _args[1];
lean_object* v_as_1629_ = _args[2];
lean_object* v_sz_1630_ = _args[3];
lean_object* v_i_1631_ = _args[4];
lean_object* v_b_1632_ = _args[5];
lean_object* v___y_1633_ = _args[6];
lean_object* v___y_1634_ = _args[7];
lean_object* v___y_1635_ = _args[8];
lean_object* v___y_1636_ = _args[9];
lean_object* v___y_1637_ = _args[10];
lean_object* v___y_1638_ = _args[11];
lean_object* v___y_1639_ = _args[12];
lean_object* v___y_1640_ = _args[13];
lean_object* v___y_1641_ = _args[14];
lean_object* v___y_1642_ = _args[15];
lean_object* v___y_1643_ = _args[16];
_start:
{
uint8_t v_a_162926__boxed_1644_; size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; lean_object* v_res_1647_; 
v_a_162926__boxed_1644_ = lean_unbox(v_a_1628_);
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1627_, v_a_162926__boxed_1644_, v_as_1629_, v_sz_boxed_1645_, v_i_boxed_1646_, v_b_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v_as_1629_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1648_, lean_object* v_ctx_1649_, uint8_t v_a_1650_, lean_object* v_n_1651_, lean_object* v_b_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
if (lean_obj_tag(v_n_1651_) == 0)
{
lean_object* v_cs_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; size_t v_sz_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v_cs_1664_ = lean_ctor_get(v_n_1651_, 0);
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v_b_1652_);
v_sz_1667_ = lean_array_size(v_cs_1664_);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1648_, v_ctx_1649_, v_a_1650_, v_cs_1664_, v_sz_1667_, v___x_1668_, v___x_1666_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1684_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1684_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1684_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_fst_1674_; 
v_fst_1674_ = lean_ctor_get(v_a_1670_, 0);
if (lean_obj_tag(v_fst_1674_) == 0)
{
lean_object* v_snd_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v_snd_1675_ = lean_ctor_get(v_a_1670_, 1);
lean_inc(v_snd_1675_);
lean_dec(v_a_1670_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_snd_1675_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1676_);
v___x_1678_ = v___x_1672_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1682_; 
lean_inc_ref(v_fst_1674_);
lean_dec(v_a_1670_);
v_val_1680_ = lean_ctor_get(v_fst_1674_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v_fst_1674_, 1);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v_val_1680_);
v___x_1682_ = v___x_1672_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_val_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1669_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1669_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
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
lean_object* v_vs_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; size_t v_sz_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v_vs_1693_ = lean_ctor_get(v_n_1651_, 0);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_b_1652_);
v_sz_1696_ = lean_array_size(v_vs_1693_);
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1649_, v_a_1650_, v_vs_1693_, v_sz_1696_, v___x_1697_, v___x_1695_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1713_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1713_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1713_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_fst_1703_; 
v_fst_1703_ = lean_ctor_get(v_a_1699_, 0);
if (lean_obj_tag(v_fst_1703_) == 0)
{
lean_object* v_snd_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v_snd_1704_ = lean_ctor_get(v_a_1699_, 1);
lean_inc(v_snd_1704_);
lean_dec(v_a_1699_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_snd_1704_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1705_);
v___x_1707_ = v___x_1701_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1711_; 
lean_inc_ref(v_fst_1703_);
lean_dec(v_a_1699_);
v_val_1709_ = lean_ctor_get(v_fst_1703_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_fst_1703_, 1);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v_val_1709_);
v___x_1711_ = v___x_1701_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_val_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1698_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1698_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1722_, lean_object* v_ctx_1723_, uint8_t v_a_1724_, lean_object* v_as_1725_, size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v_ctx_1723_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1728_);
return v___x_1741_;
}
else
{
lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1776_; 
v_snd_1742_ = lean_ctor_get(v_b_1728_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_b_1728_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v_b_1728_, 0);
lean_dec(v_unused_1777_);
v___x_1744_ = v_b_1728_;
v_isShared_1745_ = v_isSharedCheck_1776_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_dec(v_b_1728_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1776_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_a_1746_; lean_object* v___x_1747_; 
v_a_1746_ = lean_array_uget_borrowed(v_as_1725_, v_i_1727_);
lean_inc(v_snd_1742_);
lean_inc_ref(v_ctx_1723_);
v___x_1747_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1722_, v_ctx_1723_, v_a_1724_, v_a_1746_, v_snd_1742_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1767_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1767_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1767_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
if (lean_obj_tag(v_a_1748_) == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_dec_ref(v_ctx_1723_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1748_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1752_);
v___x_1754_ = v___x_1744_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_snd_1742_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1754_);
v___x_1756_ = v___x_1750_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_del_object(v___x_1750_);
lean_dec(v_snd_1742_);
v_a_1759_ = lean_ctor_get(v_a_1748_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v_a_1748_, 1);
v___x_1760_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_a_1759_);
lean_ctor_set(v___x_1744_, 0, v___x_1760_);
v___x_1762_ = v___x_1744_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_a_1759_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
size_t v___x_1763_; size_t v___x_1764_; 
v___x_1763_ = ((size_t)1ULL);
v___x_1764_ = lean_usize_add(v_i_1727_, v___x_1763_);
v_i_1727_ = v___x_1764_;
v_b_1728_ = v___x_1762_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_del_object(v___x_1744_);
lean_dec(v_snd_1742_);
lean_dec_ref(v_ctx_1723_);
v_a_1768_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1747_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1747_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1778_ = _args[0];
lean_object* v_ctx_1779_ = _args[1];
lean_object* v_a_1780_ = _args[2];
lean_object* v_as_1781_ = _args[3];
lean_object* v_sz_1782_ = _args[4];
lean_object* v_i_1783_ = _args[5];
lean_object* v_b_1784_ = _args[6];
lean_object* v___y_1785_ = _args[7];
lean_object* v___y_1786_ = _args[8];
lean_object* v___y_1787_ = _args[9];
lean_object* v___y_1788_ = _args[10];
lean_object* v___y_1789_ = _args[11];
lean_object* v___y_1790_ = _args[12];
lean_object* v___y_1791_ = _args[13];
lean_object* v___y_1792_ = _args[14];
lean_object* v___y_1793_ = _args[15];
lean_object* v___y_1794_ = _args[16];
lean_object* v___y_1795_ = _args[17];
_start:
{
uint8_t v_a_163153__boxed_1796_; size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; lean_object* v_res_1799_; 
v_a_163153__boxed_1796_ = lean_unbox(v_a_1780_);
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1782_);
lean_dec(v_sz_1782_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1783_);
lean_dec(v_i_1783_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1778_, v_ctx_1779_, v_a_163153__boxed_1796_, v_as_1781_, v_sz_boxed_1797_, v_i_boxed_1798_, v_b_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v_as_1781_);
lean_dec_ref(v_init_1778_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1800_, lean_object* v_ctx_1801_, lean_object* v_a_1802_, lean_object* v_n_1803_, lean_object* v_b_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v_a_163181__boxed_1816_; lean_object* v_res_1817_; 
v_a_163181__boxed_1816_ = lean_unbox(v_a_1802_);
v_res_1817_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1800_, v_ctx_1801_, v_a_163181__boxed_1816_, v_n_1803_, v_b_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v_n_1803_);
lean_dec_ref(v_init_1800_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1818_, uint8_t v_a_1819_, lean_object* v_t_1820_, lean_object* v_init_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_root_1833_; lean_object* v_tail_1834_; lean_object* v___x_1835_; 
v_root_1833_ = lean_ctor_get(v_t_1820_, 0);
v_tail_1834_ = lean_ctor_get(v_t_1820_, 1);
lean_inc_ref(v_ctx_1818_);
lean_inc_ref(v_init_1821_);
v___x_1835_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1821_, v_ctx_1818_, v_a_1819_, v_root_1833_, v_init_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec_ref(v_init_1821_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1872_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1872_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1872_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; 
lean_dec_ref(v_ctx_1818_);
v_a_1840_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v_a_1836_, 1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; size_t v_sz_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
lean_del_object(v___x_1838_);
v_a_1844_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v_a_1836_, 1);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_a_1844_);
v_sz_1847_ = lean_array_size(v_tail_1834_);
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1818_, v_a_1819_, v_tail_1834_, v_sz_1847_, v___x_1848_, v___x_1846_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1863_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1863_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1863_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_fst_1854_; 
v_fst_1854_ = lean_ctor_get(v_a_1850_, 0);
if (lean_obj_tag(v_fst_1854_) == 0)
{
lean_object* v_snd_1855_; lean_object* v___x_1857_; 
v_snd_1855_ = lean_ctor_get(v_a_1850_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_snd_1855_);
v___x_1857_ = v___x_1852_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_snd_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1861_; 
lean_inc_ref(v_fst_1854_);
lean_dec(v_a_1850_);
v_val_1859_ = lean_ctor_get(v_fst_1854_, 0);
lean_inc(v_val_1859_);
lean_dec_ref_known(v_fst_1854_, 1);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_val_1859_);
v___x_1861_ = v___x_1852_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_val_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1849_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1849_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_ctx_1818_);
v_a_1873_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1835_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1835_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1881_, lean_object* v_a_1882_, lean_object* v_t_1883_, lean_object* v_init_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
uint8_t v_a_163402__boxed_1896_; lean_object* v_res_1897_; 
v_a_163402__boxed_1896_ = lean_unbox(v_a_1882_);
v_res_1897_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1881_, v_a_163402__boxed_1896_, v_t_1883_, v_init_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v_t_1883_);
return v_res_1897_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1903_ = l_Lean_Name_append(v___x_1902_, v___x_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1904_, size_t v_i_1905_, size_t v_stop_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_a_1920_; uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_eq(v_i_1905_, v_stop_1906_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_array_uget_borrowed(v_as_1904_, v_i_1905_);
v___x_1926_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1925_, v___y_1908_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; uint8_t v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = lean_unbox(v_a_1927_);
lean_dec(v_a_1927_);
if (v___x_1928_ == 0)
{
if (lean_obj_tag(v___x_1925_) == 2)
{
lean_object* v_a_1929_; lean_object* v_b_1930_; lean_object* v_eq_1931_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_toCold_1987_; lean_object* v_options_1988_; uint8_t v_hasTrace_1989_; 
v_a_1929_ = lean_ctor_get(v___x_1925_, 0);
v_b_1930_ = lean_ctor_get(v___x_1925_, 1);
v_eq_1931_ = lean_ctor_get(v___x_1925_, 3);
v_toCold_1987_ = lean_ctor_get(v___y_1916_, 0);
v_options_1988_ = lean_ctor_get(v_toCold_1987_, 2);
v_hasTrace_1989_ = lean_ctor_get_uint8(v_options_1988_, sizeof(void*)*1);
if (v_hasTrace_1989_ == 0)
{
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
goto v___jp_1955_;
}
else
{
lean_object* v_inheritedTraceOptions_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_inheritedTraceOptions_1990_ = lean_ctor_get(v_toCold_1987_, 11);
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1990_, v_options_1988_, v___x_1992_);
if (v___x_1993_ == 0)
{
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_inc_ref(v_eq_1931_);
v___x_1994_ = l_Lean_MessageData_ofExpr(v_eq_1931_);
v___x_1995_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1991_, v___x_1994_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref_known(v___x_1995_, 1);
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
goto v___jp_1955_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_b_1907_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
v___jp_1932_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_box(0);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1942_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc_ref(v_eq_1931_);
v___x_1945_ = lean_grind_internalize(v_eq_1931_, v___y_1943_, v___x_1944_, v___y_1939_, v___y_1940_, v___y_1934_, v___y_1938_, v___y_1936_, v___y_1935_, v___y_1942_, v___y_1933_, v___y_1941_, v___y_1937_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref_known(v___x_1945_, 1);
lean_inc_ref(v___x_1925_);
v___x_1946_ = lean_array_push(v_b_1907_, v___x_1925_);
v_a_1920_ = v___x_1946_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_b_1907_);
v_a_1947_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1945_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
v___jp_1955_:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1929_, v___y_1956_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1930_, v___y_1956_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; uint8_t v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = lean_nat_dec_le(v_a_1967_, v_a_1969_);
if (v___x_1970_ == 0)
{
lean_dec(v_a_1969_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1958_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1965_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v___y_1956_;
v___y_1940_ = v___y_1957_;
v___y_1941_ = v___y_1964_;
v___y_1942_ = v___y_1962_;
v___y_1943_ = v_a_1967_;
goto v___jp_1932_;
}
else
{
lean_dec(v_a_1967_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1958_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1965_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v___y_1956_;
v___y_1940_ = v___y_1957_;
v___y_1941_ = v___y_1964_;
v___y_1942_ = v___y_1962_;
v___y_1943_ = v_a_1969_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_a_1967_);
lean_dec_ref(v_b_1907_);
v_a_1971_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1968_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1968_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_b_1907_);
v_a_1979_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1966_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1966_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
else
{
v_a_1920_ = v_b_1907_;
goto v___jp_1919_;
}
}
else
{
v_a_1920_ = v_b_1907_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_b_1907_);
v_a_2004_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1926_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1926_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_b_1907_);
return v___x_2012_;
}
v___jp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1905_, v___x_1921_);
v_i_1905_ = v___x_1922_;
v_b_1907_ = v_a_1920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_2013_, lean_object* v_i_2014_, lean_object* v_stop_2015_, lean_object* v_b_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
size_t v_i_boxed_2028_; size_t v_stop_boxed_2029_; lean_object* v_res_2030_; 
v_i_boxed_2028_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_stop_boxed_2029_ = lean_unbox_usize(v_stop_2015_);
lean_dec(v_stop_2015_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2013_, v_i_boxed_2028_, v_stop_boxed_2029_, v_b_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v_as_2013_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2033_, lean_object* v_start_2034_, lean_object* v_stop_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2048_ = lean_nat_dec_lt(v_start_2034_, v_stop_2035_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = lean_array_get_size(v_as_2033_);
v___x_2051_ = lean_nat_dec_le(v_stop_2035_, v___x_2050_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_nat_dec_lt(v_start_2034_, v___x_2050_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2047_);
return v___x_2053_;
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_usize_of_nat(v_start_2034_);
v___x_2055_ = lean_usize_of_nat(v___x_2050_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2033_, v___x_2054_, v___x_2055_, v___x_2047_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2056_;
}
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_usize_of_nat(v_start_2034_);
v___x_2058_ = lean_usize_of_nat(v_stop_2035_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2033_, v___x_2057_, v___x_2058_, v___x_2047_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2060_, lean_object* v_start_2061_, lean_object* v_stop_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2060_, v_start_2061_, v_stop_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v_stop_2062_);
lean_dec(v_start_2061_);
lean_dec_ref(v_as_2060_);
return v_res_2074_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_unsigned_to_nat(16u);
v___x_2077_ = lean_mk_array(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2092_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2303_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2303_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2303_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
uint8_t v_mbtc_2106_; 
v_mbtc_2106_ = lean_ctor_get_uint8(v_a_2102_, sizeof(void*)*14 + 18);
lean_dec(v_a_2102_);
if (v_mbtc_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec_ref(v_ctx_2089_);
v___x_2107_ = lean_box(v_mbtc_2106_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2109_ = v___x_2104_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2111_; 
lean_del_object(v___x_2104_);
v___x_2111_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2090_, v_a_2092_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2302_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2302_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2302_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_unbox(v_a_2112_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v_toGoalState_2118_; lean_object* v_exprs_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
lean_del_object(v___x_2114_);
v___x_2117_ = lean_st_ref_get(v_a_2090_);
v_toGoalState_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_toGoalState_2118_);
lean_dec(v___x_2117_);
v_exprs_2119_ = lean_ctor_get(v_toGoalState_2118_, 2);
lean_inc_ref(v_exprs_2119_);
lean_dec_ref(v_toGoalState_2118_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2122_ = lean_unbox(v_a_2112_);
v___x_2123_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2089_, v___x_2122_, v_exprs_2119_, v___x_2121_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec_ref(v_exprs_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2288_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2288_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2288_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_snd_2128_; lean_object* v_size_2129_; lean_object* v_buckets_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2287_; 
v_snd_2128_ = lean_ctor_get(v_a_2124_, 1);
lean_inc(v_snd_2128_);
lean_dec(v_a_2124_);
v_size_2129_ = lean_ctor_get(v_snd_2128_, 0);
v_buckets_2130_ = lean_ctor_get(v_snd_2128_, 1);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_snd_2128_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2132_ = v_snd_2128_;
v_isShared_2133_ = v_isSharedCheck_2287_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_buckets_2130_);
lean_inc(v_size_2129_);
lean_dec(v_snd_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2287_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_nat_dec_eq(v_size_2129_, v___x_2120_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_del_object(v___x_2126_);
lean_dec(v_a_2112_);
v___x_2135_ = lean_st_ref_get(v_a_2090_);
v___x_2136_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2092_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_toGoalState_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2274_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v_toGoalState_2138_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v___x_2135_, 1);
lean_dec(v_unused_2275_);
v___x_2140_ = v___x_2135_;
v_isShared_2141_ = v_isSharedCheck_2274_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_toGoalState_2138_);
lean_dec(v___x_2135_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2274_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_split_2142_; lean_object* v_splits_2143_; lean_object* v_num_2144_; uint8_t v___x_2145_; lean_object* v___y_2147_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2203_; 
v_split_2142_ = lean_ctor_get(v_toGoalState_2138_, 14);
lean_inc_ref(v_split_2142_);
lean_dec_ref(v_toGoalState_2138_);
v_splits_2143_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_splits_2143_);
lean_dec(v_a_2137_);
v_num_2144_ = lean_ctor_get(v_split_2142_, 0);
lean_inc(v_num_2144_);
lean_dec_ref(v_split_2142_);
v___x_2145_ = lean_nat_dec_lt(v_splits_2143_, v_num_2144_);
lean_dec(v_num_2144_);
lean_dec(v_splits_2143_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
lean_del_object(v___x_2140_);
lean_del_object(v___x_2132_);
v___x_2209_ = lean_mk_empty_array_with_capacity(v_size_2129_);
lean_dec(v_size_2129_);
v___x_2210_ = lean_array_get_size(v_buckets_2130_);
v___x_2211_ = lean_nat_dec_lt(v___x_2120_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_dec_ref(v_buckets_2130_);
v___y_2203_ = v___x_2209_;
goto v___jp_2202_;
}
else
{
size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = lean_usize_of_nat(v___x_2210_);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2130_, v___x_2212_, v___x_2213_, v___x_2209_);
lean_dec_ref(v_buckets_2130_);
v___y_2203_ = v___x_2214_;
goto v___jp_2202_;
}
}
else
{
lean_object* v___x_2215_; 
lean_dec_ref(v_buckets_2130_);
lean_dec(v_size_2129_);
v___x_2215_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2092_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2094_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2257_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v_verbose_2222_; 
v_verbose_2222_ = lean_ctor_get_uint8(v_a_2218_, 0);
lean_dec(v_a_2218_);
if (v_verbose_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
lean_dec(v_a_2216_);
lean_del_object(v___x_2140_);
lean_del_object(v___x_2132_);
v___x_2223_ = lean_box(v___x_2134_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2223_);
v___x_2225_ = v___x_2220_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v_splits_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_del_object(v___x_2220_);
v_splits_2227_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_splits_2227_);
lean_dec(v_a_2216_);
v___x_2228_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2229_ = l_Nat_reprFast(v_splits_2227_);
v___x_2230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v___x_2231_ = l_Lean_MessageData_ofFormat(v___x_2230_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 7);
lean_ctor_set(v___x_2140_, 1, v___x_2231_);
lean_ctor_set(v___x_2140_, 0, v___x_2228_);
v___x_2233_ = v___x_2140_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 7);
lean_ctor_set(v___x_2132_, 1, v___x_2234_);
lean_ctor_set(v___x_2132_, 0, v___x_2233_);
v___x_2236_ = v___x_2132_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Meta_Sym_reportIssue(v___x_2236_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2245_; 
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2246_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_box(v___x_2134_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2237_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
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
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2216_);
lean_del_object(v___x_2140_);
lean_del_object(v___x_2132_);
v_a_2258_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2217_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2217_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_del_object(v___x_2140_);
lean_del_object(v___x_2132_);
v_a_2266_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2215_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2215_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_array_get_size(v___y_2147_);
v___x_2149_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2147_, v___x_2120_, v___x_2148_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec_ref(v___y_2147_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2181_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2181_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2181_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_array_get_size(v_a_2150_);
v___x_2155_ = lean_nat_dec_eq(v___x_2154_, v___x_2120_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
lean_del_object(v___x_2152_);
v___x_2156_ = lean_box(0);
v_sz_2157_ = lean_array_size(v_a_2150_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2150_, v_sz_2157_, v___x_2158_, v___x_2156_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2150_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2167_; 
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2168_);
v___x_2161_ = v___x_2159_;
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2159_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_box(v_mbtc_2106_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2159_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2159_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
lean_dec(v_a_2150_);
v___x_2177_ = lean_box(v___x_2145_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2177_);
v___x_2179_ = v___x_2152_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2149_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2149_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
v___jp_2190_:
{
lean_object* v___x_2195_; 
v___x_2195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2191_, v___y_2193_, v___y_2192_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec(v___y_2191_);
v___y_2147_ = v___x_2195_;
goto v___jp_2146_;
}
v___jp_2196_:
{
uint8_t v___x_2201_; 
v___x_2201_ = lean_nat_dec_le(v___y_2200_, v___y_2198_);
if (v___x_2201_ == 0)
{
lean_dec(v___y_2198_);
lean_inc(v___y_2200_);
v___y_2191_ = v___y_2197_;
v___y_2192_ = v___y_2200_;
v___y_2193_ = v___y_2199_;
v___y_2194_ = v___y_2200_;
goto v___jp_2190_;
}
else
{
v___y_2191_ = v___y_2197_;
v___y_2192_ = v___y_2200_;
v___y_2193_ = v___y_2199_;
v___y_2194_ = v___y_2198_;
goto v___jp_2190_;
}
}
v___jp_2202_:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_array_get_size(v___y_2203_);
v___x_2205_ = lean_nat_dec_eq(v___x_2204_, v___x_2120_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = lean_nat_sub(v___x_2204_, v___x_2206_);
v___x_2208_ = lean_nat_dec_le(v___x_2120_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_inc(v___x_2207_);
v___y_2197_ = v___x_2204_;
v___y_2198_ = v___x_2207_;
v___y_2199_ = v___y_2203_;
v___y_2200_ = v___x_2207_;
goto v___jp_2196_;
}
else
{
v___y_2197_ = v___x_2204_;
v___y_2198_ = v___x_2207_;
v___y_2199_ = v___y_2203_;
v___y_2200_ = v___x_2120_;
goto v___jp_2196_;
}
}
else
{
v___y_2147_ = v___y_2203_;
goto v___jp_2146_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v___x_2135_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_buckets_2130_);
lean_dec(v_size_2129_);
v_a_2276_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2136_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2136_);
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
else
{
lean_object* v___x_2285_; 
lean_del_object(v___x_2132_);
lean_dec_ref(v_buckets_2130_);
lean_dec(v_size_2129_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v_a_2112_);
v___x_2285_ = v___x_2126_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2112_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_a_2112_);
v_a_2289_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2123_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2123_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_ctx_2089_);
v___x_2297_ = 0;
v___x_2298_ = lean_box(v___x_2297_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2298_);
v___x_2300_ = v___x_2114_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2089_);
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_ctx_2089_);
v_a_2304_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2101_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2101_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Meta_Grind_mbtc(v_ctx_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec(v_a_2313_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2325_, lean_object* v_msg_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2325_, v_msg_2326_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2339_, lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2339_, v_msg_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2353_, lean_object* v_m_2354_, lean_object* v_a_2355_, lean_object* v_b_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2354_, v_a_2355_, v_b_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2358_, lean_object* v_m_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2359_, v_a_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2362_, lean_object* v_m_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2362_, v_m_2363_, v_a_2364_);
lean_dec_ref(v_a_2364_);
lean_dec_ref(v_m_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2366_, lean_object* v_val_2367_, lean_object* v___x_2368_, lean_object* v___x_2369_, lean_object* v_as_2370_, lean_object* v_as_x27_2371_, lean_object* v_b_2372_, lean_object* v_a_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2366_, v_val_2367_, v___x_2368_, v___x_2369_, v_as_x27_2371_, v_b_2372_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2386_ = _args[0];
lean_object* v_val_2387_ = _args[1];
lean_object* v___x_2388_ = _args[2];
lean_object* v___x_2389_ = _args[3];
lean_object* v_as_2390_ = _args[4];
lean_object* v_as_x27_2391_ = _args[5];
lean_object* v_b_2392_ = _args[6];
lean_object* v_a_2393_ = _args[7];
lean_object* v___y_2394_ = _args[8];
lean_object* v___y_2395_ = _args[9];
lean_object* v___y_2396_ = _args[10];
lean_object* v___y_2397_ = _args[11];
lean_object* v___y_2398_ = _args[12];
lean_object* v___y_2399_ = _args[13];
lean_object* v___y_2400_ = _args[14];
lean_object* v___y_2401_ = _args[15];
lean_object* v___y_2402_ = _args[16];
lean_object* v___y_2403_ = _args[17];
lean_object* v___y_2404_ = _args[18];
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2386_, v_val_2387_, v___x_2388_, v___x_2389_, v_as_2390_, v_as_x27_2391_, v_b_2392_, v_a_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec(v_as_x27_2391_);
lean_dec(v_as_2390_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2406_, lean_object* v_m_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2407_, v_a_2408_, v_b_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2411_, lean_object* v_as_2412_, lean_object* v_lo_2413_, lean_object* v_hi_2414_, lean_object* v_w_2415_, lean_object* v_hlo_2416_, lean_object* v_hhi_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2411_, v_as_2412_, v_lo_2413_, v_hi_2414_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2419_, lean_object* v_as_2420_, lean_object* v_lo_2421_, lean_object* v_hi_2422_, lean_object* v_w_2423_, lean_object* v_hlo_2424_, lean_object* v_hhi_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2419_, v_as_2420_, v_lo_2421_, v_hi_2422_, v_w_2423_, v_hlo_2424_, v_hhi_2425_);
lean_dec(v_hi_2422_);
lean_dec(v_n_2419_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2427_, lean_object* v_a_2428_, lean_object* v_x_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2428_, v_x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2431_, lean_object* v_a_2432_, lean_object* v_x_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2431_, v_a_2432_, v_x_2433_);
lean_dec(v_x_2433_);
lean_dec_ref(v_a_2432_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2436_, lean_object* v_data_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2439_, lean_object* v_a_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2440_, v_x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2443_, lean_object* v_a_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2443_, v_a_2444_, v_x_2445_);
lean_dec(v_x_2445_);
lean_dec_ref(v_a_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2447_, lean_object* v_a_2448_, lean_object* v_x_2449_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2451_, lean_object* v_a_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v_res_2454_; lean_object* v_r_2455_; 
v_res_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2451_, v_a_2452_, v_x_2453_);
lean_dec(v_x_2453_);
lean_dec_ref(v_a_2452_);
v_r_2455_ = lean_box(v_res_2454_);
return v_r_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2456_, lean_object* v_data_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2459_, lean_object* v_a_2460_, lean_object* v_b_2461_, lean_object* v_x_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2460_, v_b_2461_, v_x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2464_, lean_object* v_lo_2465_, lean_object* v_hi_2466_, lean_object* v_hhi_2467_, lean_object* v_pivot_2468_, lean_object* v_as_2469_, lean_object* v_i_2470_, lean_object* v_k_2471_, lean_object* v_ilo_2472_, lean_object* v_ik_2473_, lean_object* v_w_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2466_, v_pivot_2468_, v_as_2469_, v_i_2470_, v_k_2471_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2476_, lean_object* v_lo_2477_, lean_object* v_hi_2478_, lean_object* v_hhi_2479_, lean_object* v_pivot_2480_, lean_object* v_as_2481_, lean_object* v_i_2482_, lean_object* v_k_2483_, lean_object* v_ilo_2484_, lean_object* v_ik_2485_, lean_object* v_w_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2476_, v_lo_2477_, v_hi_2478_, v_hhi_2479_, v_pivot_2480_, v_as_2481_, v_i_2482_, v_k_2483_, v_ilo_2484_, v_ik_2485_, v_w_2486_);
lean_dec_ref(v_pivot_2480_);
lean_dec(v_hi_2478_);
lean_dec(v_lo_2477_);
lean_dec(v_n_2476_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2488_, lean_object* v_i_2489_, lean_object* v_source_2490_, lean_object* v_target_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2489_, v_source_2490_, v_target_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2493_, lean_object* v_i_2494_, lean_object* v_source_2495_, lean_object* v_target_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2494_, v_source_2495_, v_target_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2499_, v_x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2503_, v_x_2504_);
return v___x_2505_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
