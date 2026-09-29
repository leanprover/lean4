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
lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_341_; 
v___x_339_ = lean_box(0);
v_a_340_ = lean_array_uget_borrowed(v_as_322_, v_i_324_);
lean_inc(v_a_340_);
v___x_341_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_340_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_341_) == 0)
{
size_t v___x_342_; size_t v___x_343_; 
lean_dec_ref_known(v___x_341_, 1);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_324_, v___x_342_);
v_i_324_ = v___x_343_;
v_b_325_ = v___x_339_;
goto _start;
}
else
{
return v___x_341_;
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
lean_object* v_ref_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_565_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 2);
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
lean_object* v___x_524_; lean_object* v_traceState_525_; lean_object* v_env_526_; lean_object* v_nextMacroScope_527_; lean_object* v_ngen_528_; lean_object* v_auxDeclNGen_529_; lean_object* v_cache_530_; lean_object* v_recordedDeps_531_; lean_object* v_messages_532_; lean_object* v_infoState_533_; lean_object* v_snapshotTasks_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_564_; 
v___x_524_ = lean_st_ref_take(v___y_516_);
v_traceState_525_ = lean_ctor_get(v___x_524_, 4);
v_env_526_ = lean_ctor_get(v___x_524_, 0);
v_nextMacroScope_527_ = lean_ctor_get(v___x_524_, 1);
v_ngen_528_ = lean_ctor_get(v___x_524_, 2);
v_auxDeclNGen_529_ = lean_ctor_get(v___x_524_, 3);
v_cache_530_ = lean_ctor_get(v___x_524_, 5);
v_recordedDeps_531_ = lean_ctor_get(v___x_524_, 6);
v_messages_532_ = lean_ctor_get(v___x_524_, 7);
v_infoState_533_ = lean_ctor_get(v___x_524_, 8);
v_snapshotTasks_534_ = lean_ctor_get(v___x_524_, 9);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_564_ == 0)
{
v___x_536_ = v___x_524_;
v_isShared_537_ = v_isSharedCheck_564_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snapshotTasks_534_);
lean_inc(v_infoState_533_);
lean_inc(v_messages_532_);
lean_inc(v_recordedDeps_531_);
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
lean_object* v___x_543_; lean_object* v___x_544_; double v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_box(0);
v___x_545_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_546_ = 0;
v___x_547_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_548_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_548_, 0, v_cls_511_);
lean_ctor_set(v___x_548_, 1, v___x_544_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
lean_ctor_set_float(v___x_548_, sizeof(void*)*3, v___x_545_);
lean_ctor_set_float(v___x_548_, sizeof(void*)*3 + 8, v___x_545_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 16, v___x_546_);
v___x_549_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_550_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v_a_520_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_inc(v_ref_518_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_ref_518_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_PersistentArray_push___redArg(v_traces_539_, v___x_551_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_552_);
v___x_554_ = v___x_541_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_552_);
lean_ctor_set_uint64(v_reuseFailAlloc_562_, sizeof(void*)*1, v_tid_538_);
v___x_554_ = v_reuseFailAlloc_562_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___x_554_);
v___x_556_ = v___x_536_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_env_526_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_527_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_528_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_cache_530_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_recordedDeps_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_messages_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_infoState_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_snapshotTasks_534_);
v___x_556_ = v_reuseFailAlloc_561_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_st_ref_put(v___y_516_, v___x_556_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_543_);
v___x_559_ = v___x_522_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_543_);
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
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_nbuckets_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_626_ = lean_array_get_size(v_data_625_);
v___x_627_ = lean_unsigned_to_nat(2u);
v_nbuckets_628_ = lean_nat_mul(v___x_626_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_box(0);
v___x_631_ = lean_mk_array(v_nbuckets_628_, v___x_630_);
v___x_632_ = lean_array_propagate_mark(v_data_625_, v___x_631_);
v___x_633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_629_, v_data_625_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_634_, lean_object* v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v_size_637_; lean_object* v_buckets_638_; lean_object* v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v_fold_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v_bkt_652_; uint8_t v___x_653_; 
v_size_637_ = lean_ctor_get(v_m_634_, 0);
v_buckets_638_ = lean_ctor_get(v_m_634_, 1);
v___x_639_ = lean_array_get_size(v_buckets_638_);
v___x_640_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_635_);
v___x_641_ = 32ULL;
v___x_642_ = lean_uint64_shift_right(v___x_640_, v___x_641_);
v_fold_643_ = lean_uint64_xor(v___x_640_, v___x_642_);
v___x_644_ = 16ULL;
v___x_645_ = lean_uint64_shift_right(v_fold_643_, v___x_644_);
v___x_646_ = lean_uint64_xor(v_fold_643_, v___x_645_);
v___x_647_ = lean_uint64_to_usize(v___x_646_);
v___x_648_ = lean_usize_of_nat(v___x_639_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_sub(v___x_648_, v___x_649_);
v___x_651_ = lean_usize_land(v___x_647_, v___x_650_);
v_bkt_652_ = lean_array_uget_borrowed(v_buckets_638_, v___x_651_);
v___x_653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_635_, v_bkt_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_674_; 
lean_inc_ref(v_buckets_638_);
lean_inc(v_size_637_);
v_isSharedCheck_674_ = !lean_is_exclusive(v_m_634_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_675_ = lean_ctor_get(v_m_634_, 1);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_m_634_, 0);
lean_dec(v_unused_676_);
v___x_655_ = v_m_634_;
v_isShared_656_ = v_isSharedCheck_674_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_m_634_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_674_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v_size_x27_658_; lean_object* v___x_659_; lean_object* v_buckets_x27_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v_size_x27_658_ = lean_nat_add(v_size_637_, v___x_657_);
lean_dec(v_size_637_);
lean_inc(v_bkt_652_);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v_a_635_);
lean_ctor_set(v___x_659_, 1, v_b_636_);
lean_ctor_set(v___x_659_, 2, v_bkt_652_);
v_buckets_x27_660_ = lean_array_uset(v_buckets_638_, v___x_651_, v___x_659_);
v___x_661_ = lean_unsigned_to_nat(4u);
v___x_662_ = lean_nat_mul(v_size_x27_658_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = lean_nat_div(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_array_get_size(v_buckets_x27_660_);
v___x_666_ = lean_nat_dec_le(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
if (v___x_666_ == 0)
{
lean_object* v_val_667_; lean_object* v___x_669_; 
v_val_667_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_660_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_val_667_);
lean_ctor_set(v___x_655_, 0, v_size_x27_658_);
v___x_669_ = v___x_655_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_size_x27_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_val_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v___x_672_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_buckets_x27_660_);
lean_ctor_set(v___x_655_, 0, v_size_x27_658_);
v___x_672_ = v___x_655_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_size_x27_658_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_buckets_x27_660_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_dec(v_b_636_);
lean_dec_ref(v_a_635_);
return v_m_634_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_ctx_677_, lean_object* v_val_678_, lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v_as_x27_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
if (lean_obj_tag(v_as_x27_681_) == 0)
{
lean_object* v___x_694_; 
lean_dec(v___x_680_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_val_678_);
lean_dec_ref(v_ctx_677_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_b_682_);
return v___x_694_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v_eqAssignment_697_; lean_object* v_arg_698_; lean_object* v___x_699_; 
v_head_695_ = lean_ctor_get(v_as_x27_681_, 0);
v_tail_696_ = lean_ctor_get(v_as_x27_681_, 1);
v_eqAssignment_697_ = lean_ctor_get(v_ctx_677_, 2);
v_arg_698_ = lean_ctor_get(v_head_695_, 0);
lean_inc_ref(v_eqAssignment_697_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
lean_inc(v___y_684_);
lean_inc(v___y_683_);
lean_inc_ref(v_arg_698_);
lean_inc_ref(v_val_678_);
v___x_699_ = lean_apply_13(v_eqAssignment_697_, v_val_678_, v_arg_698_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, lean_box(0));
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
if (v___x_701_ == 0)
{
v_as_x27_681_ = v_tail_696_;
goto _start;
}
else
{
lean_object* v___x_703_; 
lean_inc_ref(v_arg_698_);
lean_inc_ref(v_val_678_);
v___x_703_ = l_Lean_Meta_Grind_hasSameType(v_val_678_, v_arg_698_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; uint8_t v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
if (v___x_705_ == 0)
{
v_as_x27_681_ = v_tail_696_;
goto _start;
}
else
{
lean_object* v___x_707_; 
lean_inc(v___x_680_);
lean_inc(v_head_695_);
lean_inc_ref(v___x_679_);
v___x_707_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_679_, v_head_695_, v___x_680_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_box(0);
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_682_, v_a_708_, v___x_709_);
v_as_x27_681_ = v_tail_696_;
v_b_682_ = v___x_710_;
goto _start;
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_b_682_);
lean_dec(v___x_680_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_val_678_);
lean_dec_ref(v_ctx_677_);
v_a_712_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_707_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_707_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v_b_682_);
lean_dec(v___x_680_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_val_678_);
lean_dec_ref(v_ctx_677_);
v_a_720_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_703_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_703_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v_b_682_);
lean_dec(v___x_680_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_val_678_);
lean_dec_ref(v_ctx_677_);
v_a_728_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_699_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_699_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_ctx_736_ = _args[0];
lean_object* v_val_737_ = _args[1];
lean_object* v___x_738_ = _args[2];
lean_object* v___x_739_ = _args[3];
lean_object* v_as_x27_740_ = _args[4];
lean_object* v_b_741_ = _args[5];
lean_object* v___y_742_ = _args[6];
lean_object* v___y_743_ = _args[7];
lean_object* v___y_744_ = _args[8];
lean_object* v___y_745_ = _args[9];
lean_object* v___y_746_ = _args[10];
lean_object* v___y_747_ = _args[11];
lean_object* v___y_748_ = _args[12];
lean_object* v___y_749_ = _args[13];
lean_object* v___y_750_ = _args[14];
lean_object* v___y_751_ = _args[15];
lean_object* v___y_752_ = _args[16];
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_736_, v_val_737_, v___x_738_, v___x_739_, v_as_x27_740_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v_as_x27_740_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* v_a_754_, lean_object* v_b_755_, lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_dec(v_b_755_);
lean_dec_ref(v_a_754_);
return v_x_756_;
}
else
{
lean_object* v_key_757_; lean_object* v_value_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_771_; 
v_key_757_ = lean_ctor_get(v_x_756_, 0);
v_value_758_ = lean_ctor_get(v_x_756_, 1);
v_tail_759_ = lean_ctor_get(v_x_756_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_771_ == 0)
{
v___x_761_ = v_x_756_;
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_value_758_);
lean_inc(v_key_757_);
lean_dec(v_x_756_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_expr_eqv(v_key_757_, v_a_754_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_754_, v_b_755_, v_tail_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_key_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_value_758_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_769_; 
lean_dec(v_value_758_);
lean_dec(v_key_757_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_b_755_);
lean_ctor_set(v___x_761_, 0, v_a_754_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_754_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_b_755_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_tail_759_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
else
{
lean_object* v_key_775_; lean_object* v_tail_776_; uint8_t v___x_777_; 
v_key_775_ = lean_ctor_get(v_x_773_, 0);
v_tail_776_ = lean_ctor_get(v_x_773_, 2);
v___x_777_ = lean_expr_eqv(v_key_775_, v_a_772_);
if (v___x_777_ == 0)
{
v_x_773_ = v_tail_776_;
goto _start;
}
else
{
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* v_a_779_, lean_object* v_x_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_779_, v_x_780_);
lean_dec(v_x_780_);
lean_dec_ref(v_a_779_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
return v_x_783_;
}
else
{
lean_object* v_key_785_; lean_object* v_value_786_; lean_object* v_tail_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_810_; 
v_key_785_ = lean_ctor_get(v_x_784_, 0);
v_value_786_ = lean_ctor_get(v_x_784_, 1);
v_tail_787_ = lean_ctor_get(v_x_784_, 2);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_810_ == 0)
{
v___x_789_ = v_x_784_;
v_isShared_790_ = v_isSharedCheck_810_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_tail_787_);
lean_inc(v_value_786_);
lean_inc(v_key_785_);
lean_dec(v_x_784_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_810_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v_fold_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_791_ = lean_array_get_size(v_x_783_);
v___x_792_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_785_);
v___x_793_ = 32ULL;
v___x_794_ = lean_uint64_shift_right(v___x_792_, v___x_793_);
v_fold_795_ = lean_uint64_xor(v___x_792_, v___x_794_);
v___x_796_ = 16ULL;
v___x_797_ = lean_uint64_shift_right(v_fold_795_, v___x_796_);
v___x_798_ = lean_uint64_xor(v_fold_795_, v___x_797_);
v___x_799_ = lean_uint64_to_usize(v___x_798_);
v___x_800_ = lean_usize_of_nat(v___x_791_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_sub(v___x_800_, v___x_801_);
v___x_803_ = lean_usize_land(v___x_799_, v___x_802_);
v___x_804_ = lean_array_uget_borrowed(v_x_783_, v___x_803_);
lean_inc(v___x_804_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___x_804_);
v___x_806_ = v___x_789_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_key_785_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_value_786_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v___x_804_);
v___x_806_ = v_reuseFailAlloc_809_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_array_uset(v_x_783_, v___x_803_, v___x_806_);
v_x_783_ = v___x_807_;
v_x_784_ = v_tail_787_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* v_i_811_, lean_object* v_source_812_, lean_object* v_target_813_){
_start:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_array_get_size(v_source_812_);
v___x_815_ = lean_nat_dec_lt(v_i_811_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec_ref(v_source_812_);
lean_dec(v_i_811_);
return v_target_813_;
}
else
{
lean_object* v_es_816_; lean_object* v___x_817_; lean_object* v_source_818_; lean_object* v_target_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_es_816_ = lean_array_fget(v_source_812_, v_i_811_);
v___x_817_ = lean_box(0);
v_source_818_ = lean_array_fset(v_source_812_, v_i_811_, v___x_817_);
v_target_819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_813_, v_es_816_);
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = lean_nat_add(v_i_811_, v___x_820_);
lean_dec(v_i_811_);
v_i_811_ = v___x_821_;
v_source_812_ = v_source_818_;
v_target_813_ = v_target_819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* v_data_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_nbuckets_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_824_ = lean_array_get_size(v_data_823_);
v___x_825_ = lean_unsigned_to_nat(2u);
v_nbuckets_826_ = lean_nat_mul(v___x_824_, v___x_825_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_box(0);
v___x_829_ = lean_mk_array(v_nbuckets_826_, v___x_828_);
v___x_830_ = lean_array_propagate_mark(v_data_823_, v___x_829_);
v___x_831_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_827_, v_data_823_, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_832_, lean_object* v_a_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_size_835_; lean_object* v_buckets_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_879_; 
v_size_835_ = lean_ctor_get(v_m_832_, 0);
v_buckets_836_ = lean_ctor_get(v_m_832_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_m_832_);
if (v_isSharedCheck_879_ == 0)
{
v___x_838_ = v_m_832_;
v_isShared_839_ = v_isSharedCheck_879_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_buckets_836_);
lean_inc(v_size_835_);
lean_dec(v_m_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_879_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; uint64_t v___x_841_; uint64_t v___x_842_; uint64_t v___x_843_; uint64_t v_fold_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v_bkt_853_; uint8_t v___x_854_; 
v___x_840_ = lean_array_get_size(v_buckets_836_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_833_);
v___x_842_ = 32ULL;
v___x_843_ = lean_uint64_shift_right(v___x_841_, v___x_842_);
v_fold_844_ = lean_uint64_xor(v___x_841_, v___x_843_);
v___x_845_ = 16ULL;
v___x_846_ = lean_uint64_shift_right(v_fold_844_, v___x_845_);
v___x_847_ = lean_uint64_xor(v_fold_844_, v___x_846_);
v___x_848_ = lean_uint64_to_usize(v___x_847_);
v___x_849_ = lean_usize_of_nat(v___x_840_);
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_sub(v___x_849_, v___x_850_);
v___x_852_ = lean_usize_land(v___x_848_, v___x_851_);
v_bkt_853_ = lean_array_uget_borrowed(v_buckets_836_, v___x_852_);
v___x_854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_833_, v_bkt_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v_size_x27_856_; lean_object* v___x_857_; lean_object* v_buckets_x27_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_855_ = lean_unsigned_to_nat(1u);
v_size_x27_856_ = lean_nat_add(v_size_835_, v___x_855_);
lean_dec(v_size_835_);
lean_inc(v_bkt_853_);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v_a_833_);
lean_ctor_set(v___x_857_, 1, v_b_834_);
lean_ctor_set(v___x_857_, 2, v_bkt_853_);
v_buckets_x27_858_ = lean_array_uset(v_buckets_836_, v___x_852_, v___x_857_);
v___x_859_ = lean_unsigned_to_nat(4u);
v___x_860_ = lean_nat_mul(v_size_x27_856_, v___x_859_);
v___x_861_ = lean_unsigned_to_nat(3u);
v___x_862_ = lean_nat_div(v___x_860_, v___x_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_array_get_size(v_buckets_x27_858_);
v___x_864_ = lean_nat_dec_le(v___x_862_, v___x_863_);
lean_dec(v___x_862_);
if (v___x_864_ == 0)
{
lean_object* v_val_865_; lean_object* v___x_867_; 
v_val_865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_858_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_val_865_);
lean_ctor_set(v___x_838_, 0, v_size_x27_856_);
v___x_867_ = v___x_838_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_size_x27_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_val_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
else
{
lean_object* v___x_870_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_buckets_x27_858_);
lean_ctor_set(v___x_838_, 0, v_size_x27_856_);
v___x_870_ = v___x_838_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_size_x27_856_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_buckets_x27_858_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v___x_872_; lean_object* v_buckets_x27_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
lean_inc(v_bkt_853_);
v___x_872_ = lean_box(0);
v_buckets_x27_873_ = lean_array_uset(v_buckets_836_, v___x_852_, v___x_872_);
v___x_874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_833_, v_b_834_, v_bkt_853_);
v___x_875_ = lean_array_uset(v_buckets_x27_873_, v___x_852_, v___x_874_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_875_);
v___x_877_ = v___x_838_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_size_835_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
uint8_t v___x_882_; 
v___x_882_ = 0;
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v_arg_885_; size_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v_head_883_ = lean_ctor_get(v_x_881_, 0);
v_tail_884_ = lean_ctor_get(v_x_881_, 1);
v_arg_885_ = lean_ctor_get(v_head_883_, 0);
v___x_886_ = lean_ptr_addr(v_val_880_);
v___x_887_ = lean_ptr_addr(v_arg_885_);
v___x_888_ = lean_usize_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
v_x_881_ = v_tail_884_;
goto _start;
}
else
{
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_890_, lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_890_, v_x_891_);
lean_dec(v_x_891_);
lean_dec_ref(v_val_890_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_906_ = l_Lean_Name_append(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_913_, lean_object* v_ctx_914_, lean_object* v___x_915_, lean_object* v_as_916_, size_t v_sz_917_, size_t v_i_918_, lean_object* v_b_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_a_932_; uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_918_, v_sz_917_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec_ref(v___x_915_);
lean_dec_ref(v_ctx_914_);
lean_dec_ref(v_e_913_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_919_);
return v___x_937_;
}
else
{
lean_object* v_snd_938_; lean_object* v_fst_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1051_; 
v_snd_938_ = lean_ctor_get(v_b_919_, 1);
v_fst_939_ = lean_ctor_get(v_b_919_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_b_919_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_941_ = v_b_919_;
v_isShared_942_ = v_isSharedCheck_1051_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_938_);
lean_inc(v_fst_939_);
lean_dec(v_b_919_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1051_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1050_; 
v_fst_943_ = lean_ctor_get(v_snd_938_, 0);
v_snd_944_ = lean_ctor_get(v_snd_938_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_snd_938_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_946_ = v_snd_938_;
v_isShared_947_ = v_isSharedCheck_1050_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_inc(v_fst_943_);
lean_dec(v_snd_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1050_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_map_949_; lean_object* v_candidates_950_; lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_959_ = lean_array_uget_borrowed(v_as_916_, v_i_918_);
v___x_960_ = lean_st_ref_get(v___y_920_);
v___x_961_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_960_, v_a_959_);
lean_dec(v___x_960_);
if (lean_obj_tag(v___x_961_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1047_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_1047_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1047_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v_hasTheoryVar_1006_; lean_object* v___x_1007_; 
v_hasTheoryVar_1006_ = lean_ctor_get(v_ctx_914_, 1);
lean_inc_ref(v_hasTheoryVar_1006_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc(v___y_920_);
lean_inc(v_val_962_);
v___x_1007_ = lean_apply_12(v_hasTheoryVar_1006_, v_val_962_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, lean_box(0));
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; uint8_t v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_unbox(v_a_1008_);
lean_dec(v_a_1008_);
if (v___x_1009_ == 0)
{
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
v_map_949_ = v_fst_939_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
else
{
lean_object* v_toCold_1010_; lean_object* v_options_1011_; uint8_t v_hasTrace_1012_; 
v_toCold_1010_ = lean_ctor_get(v___y_928_, 0);
v_options_1011_ = lean_ctor_get(v_toCold_1010_, 2);
v_hasTrace_1012_ = lean_ctor_get_uint8(v_options_1011_, sizeof(void*)*1);
if (v_hasTrace_1012_ == 0)
{
lean_del_object(v___x_964_);
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
goto v___jp_966_;
}
else
{
lean_object* v_inheritedTraceOptions_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_inheritedTraceOptions_1013_ = lean_ctor_get(v_toCold_1010_, 11);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1016_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1013_, v_options_1011_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_del_object(v___x_964_);
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_inc(v_val_962_);
v___x_1017_ = l_Lean_MessageData_ofExpr(v_val_962_);
v___x_1018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_inc_ref(v___x_915_);
v___x_1020_ = l_Lean_MessageData_ofExpr(v___x_915_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_inc(v_snd_944_);
v___x_1024_ = l_Nat_reprFast(v_snd_944_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 3);
lean_ctor_set(v___x_964_, 0, v___x_1024_);
v___x_1026_ = v___x_964_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1014_, v___x_1028_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref_known(v___x_1029_, 1);
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
goto v___jp_966_;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_val_962_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_915_);
lean_dec_ref(v_ctx_914_);
lean_dec_ref(v_e_913_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
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
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_915_);
lean_dec_ref(v_ctx_914_);
lean_dec_ref(v_e_913_);
v_a_1039_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1007_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1007_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
v___jp_966_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref_n(v_e_913_, 2);
lean_inc(v_val_962_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_val_962_);
lean_ctor_set(v___x_977_, 1, v_e_913_);
v___x_978_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_913_, v_snd_944_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_939_, v_a_979_);
if (lean_obj_tag(v___x_980_) == 1)
{
lean_object* v_val_981_; uint8_t v___x_982_; 
v_val_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_962_, v_val_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_inc(v_snd_944_);
lean_inc_ref(v___x_977_);
lean_inc_ref(v_ctx_914_);
v___x_983_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_914_, v_val_962_, v___x_977_, v_snd_944_, v_val_981_, v_fst_943_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_977_);
lean_ctor_set(v___x_985_, 1, v_val_981_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_939_, v_a_979_, v___x_985_);
v_map_949_ = v___x_986_;
v_candidates_950_ = v_a_984_;
goto v___jp_948_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_val_981_);
lean_dec(v_a_979_);
lean_dec_ref_known(v___x_977_, 2);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_915_);
lean_dec_ref(v_ctx_914_);
lean_dec_ref(v_e_913_);
v_a_987_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_983_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_dec(v_val_981_);
lean_dec(v_a_979_);
lean_dec_ref_known(v___x_977_, 2);
lean_dec(v_val_962_);
v_map_949_ = v_fst_939_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v___x_980_);
lean_dec(v_val_962_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_977_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_939_, v_a_979_, v___x_996_);
v_map_949_ = v___x_997_;
v_candidates_950_ = v_fst_943_;
goto v___jp_948_;
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref_known(v___x_977_, 2);
lean_dec(v_val_962_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec(v_fst_943_);
lean_del_object(v___x_941_);
lean_dec(v_fst_939_);
lean_dec_ref(v___x_915_);
lean_dec_ref(v_ctx_914_);
lean_dec_ref(v_e_913_);
v_a_998_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_978_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_978_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v___x_961_);
lean_del_object(v___x_946_);
lean_del_object(v___x_941_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_fst_943_);
lean_ctor_set(v___x_1048_, 1, v_snd_944_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_fst_939_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v_a_932_ = v___x_1049_;
goto v___jp_931_;
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
v_a_932_ = v___x_956_;
goto v___jp_931_;
}
}
}
}
}
}
v___jp_931_:
{
size_t v___x_933_; size_t v___x_934_; 
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_918_, v___x_933_);
v_i_918_ = v___x_934_;
v_b_919_ = v_a_932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1052_ = _args[0];
lean_object* v_ctx_1053_ = _args[1];
lean_object* v___x_1054_ = _args[2];
lean_object* v_as_1055_ = _args[3];
lean_object* v_sz_1056_ = _args[4];
lean_object* v_i_1057_ = _args[5];
lean_object* v_b_1058_ = _args[6];
lean_object* v___y_1059_ = _args[7];
lean_object* v___y_1060_ = _args[8];
lean_object* v___y_1061_ = _args[9];
lean_object* v___y_1062_ = _args[10];
lean_object* v___y_1063_ = _args[11];
lean_object* v___y_1064_ = _args[12];
lean_object* v___y_1065_ = _args[13];
lean_object* v___y_1066_ = _args[14];
lean_object* v___y_1067_ = _args[15];
lean_object* v___y_1068_ = _args[16];
lean_object* v___y_1069_ = _args[17];
_start:
{
size_t v_sz_boxed_1070_; size_t v_i_boxed_1071_; lean_object* v_res_1072_; 
v_sz_boxed_1070_ = lean_unbox_usize(v_sz_1056_);
lean_dec(v_sz_1056_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1052_, v_ctx_1053_, v___x_1054_, v_as_1055_, v_sz_boxed_1070_, v_i_boxed_1071_, v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v_as_1055_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1073_, uint8_t v_a_1074_, lean_object* v_as_1075_, size_t v_sz_1076_, size_t v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_usize_dec_lt(v_i_1077_, v_sz_1076_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v_ctx_1073_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_b_1078_);
return v___x_1091_;
}
else
{
lean_object* v_snd_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1194_; 
v_snd_1092_ = lean_ctor_get(v_b_1078_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_b_1078_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_b_1078_, 0);
lean_dec(v_unused_1195_);
v___x_1094_ = v_b_1078_;
v_isShared_1095_ = v_isSharedCheck_1194_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_snd_1092_);
lean_dec(v_b_1078_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1194_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1193_; 
v_fst_1096_ = lean_ctor_get(v_snd_1092_, 0);
v_snd_1097_ = lean_ctor_get(v_snd_1092_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_snd_1092_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1099_ = v_snd_1092_;
v_isShared_1100_ = v_isSharedCheck_1193_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v_snd_1092_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1193_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v_a_1103_; lean_object* v_a_1116_; uint8_t v___y_1190_; uint8_t v___x_1191_; 
v___x_1101_ = lean_box(0);
v_a_1116_ = lean_array_uget_borrowed(v_as_1075_, v_i_1077_);
v___x_1191_ = l_Lean_Expr_isApp(v_a_1116_);
if (v___x_1191_ == 0)
{
v___y_1190_ = v_a_1074_;
goto v___jp_1189_;
}
else
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Lean_Expr_isEq(v_a_1116_);
if (v___x_1192_ == 0)
{
goto v___jp_1117_;
}
else
{
v___y_1190_ = v_a_1074_;
goto v___jp_1189_;
}
}
v___jp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v_a_1103_);
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1105_ = v___x_1099_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_a_1103_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
size_t v___x_1106_; size_t v___x_1107_; 
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_add(v_i_1077_, v___x_1106_);
v_i_1077_ = v___x_1107_;
v_b_1078_ = v___x_1105_;
goto _start;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_snd_1097_);
lean_ctor_set(v___x_1094_, 0, v_fst_1096_);
v___x_1112_ = v___x_1094_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_fst_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_snd_1097_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v_a_1103_ = v___x_1112_;
goto v___jp_1102_;
}
}
v___jp_1114_:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_fst_1096_);
lean_ctor_set(v___x_1115_, 1, v_snd_1097_);
v_a_1103_ = v___x_1115_;
goto v___jp_1102_;
}
v___jp_1117_:
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Lean_Expr_isHEq(v_a_1116_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_inc(v_a_1116_);
v___x_1119_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1116_, v___y_1079_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; uint8_t v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1094_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_fst_1096_);
lean_ctor_set(v___x_1122_, 1, v_snd_1097_);
v_a_1103_ = v___x_1122_;
goto v___jp_1102_;
}
else
{
lean_object* v_isInterpreted_1123_; lean_object* v___x_1124_; 
v_isInterpreted_1123_ = lean_ctor_get(v_ctx_1073_, 0);
lean_inc_ref(v_isInterpreted_1123_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc(v_a_1116_);
v___x_1124_ = lean_apply_12(v_isInterpreted_1123_, v_a_1116_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, lean_box(0));
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; uint8_t v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = lean_unbox(v_a_1125_);
lean_dec(v_a_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = l_Lean_Expr_getAppFn(v_a_1116_);
lean_inc_ref(v___x_1127_);
v___x_1128_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1127_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; uint8_t v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v_dummy_1133_; lean_object* v_nargs_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; size_t v_sz_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
lean_del_object(v___x_1094_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v_dummy_1133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1134_ = l_Lean_Expr_getAppNumArgs(v_a_1116_);
lean_inc(v_nargs_1134_);
v___x_1135_ = lean_mk_array(v_nargs_1134_, v_dummy_1133_);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_sub(v_nargs_1134_, v___x_1136_);
lean_dec(v_nargs_1134_);
lean_inc_n(v_a_1116_, 2);
v___x_1138_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1116_, v___x_1135_, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_snd_1097_);
lean_ctor_set(v___x_1139_, 1, v___x_1132_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_fst_1096_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v_sz_1141_ = lean_array_size(v___x_1138_);
v___x_1142_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1073_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1116_, v_ctx_1073_, v___x_1127_, v___x_1138_, v_sz_1141_, v___x_1142_, v___x_1140_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec_ref(v___x_1138_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_snd_1145_; lean_object* v_fst_1146_; lean_object* v_fst_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v_snd_1145_ = lean_ctor_get(v_a_1144_, 1);
lean_inc(v_snd_1145_);
v_fst_1146_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_fst_1146_);
lean_dec(v_a_1144_);
v_fst_1147_ = lean_ctor_get(v_snd_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_snd_1145_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_snd_1145_, 1);
lean_dec(v_unused_1155_);
v___x_1149_ = v_snd_1145_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_fst_1147_);
lean_dec(v_snd_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_fst_1147_);
lean_ctor_set(v___x_1149_, 0, v_fst_1146_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_fst_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_fst_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v_a_1103_ = v___x_1152_;
goto v___jp_1102_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_del_object(v___x_1099_);
lean_dec_ref(v_ctx_1073_);
v_a_1156_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1143_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1143_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_dec_ref(v___x_1127_);
goto v___jp_1110_;
}
}
else
{
lean_dec_ref(v___x_1127_);
goto v___jp_1110_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v___x_1127_);
lean_del_object(v___x_1099_);
lean_dec(v_snd_1097_);
lean_dec(v_fst_1096_);
lean_del_object(v___x_1094_);
lean_dec_ref(v_ctx_1073_);
v_a_1164_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1128_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1128_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v___x_1172_; 
lean_del_object(v___x_1094_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_fst_1096_);
lean_ctor_set(v___x_1172_, 1, v_snd_1097_);
v_a_1103_ = v___x_1172_;
goto v___jp_1102_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1099_);
lean_dec(v_snd_1097_);
lean_dec(v_fst_1096_);
lean_del_object(v___x_1094_);
lean_dec_ref(v_ctx_1073_);
v_a_1173_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1124_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1124_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_del_object(v___x_1099_);
lean_dec(v_snd_1097_);
lean_dec(v_fst_1096_);
lean_del_object(v___x_1094_);
lean_dec_ref(v_ctx_1073_);
v_a_1181_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1119_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1119_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_del_object(v___x_1094_);
goto v___jp_1114_;
}
}
v___jp_1189_:
{
if (v___y_1190_ == 0)
{
lean_del_object(v___x_1094_);
goto v___jp_1114_;
}
else
{
goto v___jp_1117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object** _args){
lean_object* v_ctx_1196_ = _args[0];
lean_object* v_a_1197_ = _args[1];
lean_object* v_as_1198_ = _args[2];
lean_object* v_sz_1199_ = _args[3];
lean_object* v_i_1200_ = _args[4];
lean_object* v_b_1201_ = _args[5];
lean_object* v___y_1202_ = _args[6];
lean_object* v___y_1203_ = _args[7];
lean_object* v___y_1204_ = _args[8];
lean_object* v___y_1205_ = _args[9];
lean_object* v___y_1206_ = _args[10];
lean_object* v___y_1207_ = _args[11];
lean_object* v___y_1208_ = _args[12];
lean_object* v___y_1209_ = _args[13];
lean_object* v___y_1210_ = _args[14];
lean_object* v___y_1211_ = _args[15];
lean_object* v___y_1212_ = _args[16];
_start:
{
uint8_t v_a_162409__boxed_1213_; size_t v_sz_boxed_1214_; size_t v_i_boxed_1215_; lean_object* v_res_1216_; 
v_a_162409__boxed_1213_ = lean_unbox(v_a_1197_);
v_sz_boxed_1214_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1215_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1196_, v_a_162409__boxed_1213_, v_as_1198_, v_sz_boxed_1214_, v_i_boxed_1215_, v_b_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v_as_1198_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1217_, uint8_t v_a_1218_, lean_object* v_as_1219_, size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_ctx_1217_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1222_);
return v___x_1235_;
}
else
{
lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1338_; 
v_snd_1236_ = lean_ctor_get(v_b_1222_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_b_1222_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_b_1222_, 0);
lean_dec(v_unused_1339_);
v___x_1238_ = v_b_1222_;
v_isShared_1239_ = v_isSharedCheck_1338_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_dec(v_b_1222_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1338_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1337_; 
v_fst_1240_ = lean_ctor_get(v_snd_1236_, 0);
v_snd_1241_ = lean_ctor_get(v_snd_1236_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_snd_1236_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1243_ = v_snd_1236_;
v_isShared_1244_ = v_isSharedCheck_1337_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_snd_1236_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1337_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v_a_1247_; lean_object* v_a_1260_; uint8_t v___y_1334_; uint8_t v___x_1335_; 
v___x_1245_ = lean_box(0);
v_a_1260_ = lean_array_uget_borrowed(v_as_1219_, v_i_1221_);
v___x_1335_ = l_Lean_Expr_isApp(v_a_1260_);
if (v___x_1335_ == 0)
{
v___y_1334_ = v_a_1218_;
goto v___jp_1333_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_Expr_isEq(v_a_1260_);
if (v___x_1336_ == 0)
{
goto v___jp_1261_;
}
else
{
v___y_1334_ = v_a_1218_;
goto v___jp_1333_;
}
}
v___jp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v_a_1247_);
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_a_1247_);
v___x_1249_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1221_, v___x_1250_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1217_, v_a_1218_, v_as_1219_, v_sz_1220_, v___x_1251_, v___x_1249_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1252_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_snd_1241_);
lean_ctor_set(v___x_1238_, 0, v_fst_1240_);
v___x_1256_ = v___x_1238_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1240_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_snd_1241_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_a_1247_ = v___x_1256_;
goto v___jp_1246_;
}
}
v___jp_1258_:
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_fst_1240_);
lean_ctor_set(v___x_1259_, 1, v_snd_1241_);
v_a_1247_ = v___x_1259_;
goto v___jp_1246_;
}
v___jp_1261_:
{
uint8_t v___x_1262_; 
v___x_1262_ = l_Lean_Expr_isHEq(v_a_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_inc(v_a_1260_);
v___x_1263_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1260_, v___y_1223_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; uint8_t v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = lean_unbox(v_a_1264_);
lean_dec(v_a_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_del_object(v___x_1238_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_fst_1240_);
lean_ctor_set(v___x_1266_, 1, v_snd_1241_);
v_a_1247_ = v___x_1266_;
goto v___jp_1246_;
}
else
{
lean_object* v_isInterpreted_1267_; lean_object* v___x_1268_; 
v_isInterpreted_1267_ = lean_ctor_get(v_ctx_1217_, 0);
lean_inc_ref(v_isInterpreted_1267_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1227_);
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc(v_a_1260_);
v___x_1268_ = lean_apply_12(v_isInterpreted_1267_, v_a_1260_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Lean_Expr_getAppFn(v_a_1260_);
lean_inc_ref(v___x_1271_);
v___x_1272_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1271_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; uint8_t v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1274_ == 0)
{
uint8_t v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1271_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v_dummy_1277_; lean_object* v_nargs_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; size_t v_sz_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1238_);
v___x_1276_ = lean_unsigned_to_nat(0u);
v_dummy_1277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1278_ = l_Lean_Expr_getAppNumArgs(v_a_1260_);
lean_inc(v_nargs_1278_);
v___x_1279_ = lean_mk_array(v_nargs_1278_, v_dummy_1277_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_sub(v_nargs_1278_, v___x_1280_);
lean_dec(v_nargs_1278_);
lean_inc_n(v_a_1260_, 2);
v___x_1282_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1260_, v___x_1279_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_snd_1241_);
lean_ctor_set(v___x_1283_, 1, v___x_1276_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_fst_1240_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v_sz_1285_ = lean_array_size(v___x_1282_);
v___x_1286_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1217_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1260_, v_ctx_1217_, v___x_1271_, v___x_1282_, v_sz_1285_, v___x_1286_, v___x_1284_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec_ref(v___x_1282_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_snd_1289_; lean_object* v_fst_1290_; lean_object* v_fst_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_snd_1289_ = lean_ctor_get(v_a_1288_, 1);
lean_inc(v_snd_1289_);
v_fst_1290_ = lean_ctor_get(v_a_1288_, 0);
lean_inc(v_fst_1290_);
lean_dec(v_a_1288_);
v_fst_1291_ = lean_ctor_get(v_snd_1289_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_snd_1289_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_snd_1289_, 1);
lean_dec(v_unused_1299_);
v___x_1293_ = v_snd_1289_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_fst_1291_);
lean_dec(v_snd_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_fst_1291_);
lean_ctor_set(v___x_1293_, 0, v_fst_1290_);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_fst_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_fst_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v_a_1247_ = v___x_1296_;
goto v___jp_1246_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_del_object(v___x_1243_);
lean_dec_ref(v_ctx_1217_);
v_a_1300_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1287_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1287_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_dec_ref(v___x_1271_);
goto v___jp_1254_;
}
}
else
{
lean_dec_ref(v___x_1271_);
goto v___jp_1254_;
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v___x_1271_);
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_del_object(v___x_1238_);
lean_dec_ref(v_ctx_1217_);
v_a_1308_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1272_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1272_);
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
else
{
lean_object* v___x_1316_; 
lean_del_object(v___x_1238_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_fst_1240_);
lean_ctor_set(v___x_1316_, 1, v_snd_1241_);
v_a_1247_ = v___x_1316_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_del_object(v___x_1238_);
lean_dec_ref(v_ctx_1217_);
v_a_1317_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1268_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1268_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_del_object(v___x_1238_);
lean_dec_ref(v_ctx_1217_);
v_a_1325_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1263_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1263_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_del_object(v___x_1238_);
goto v___jp_1258_;
}
}
v___jp_1333_:
{
if (v___y_1334_ == 0)
{
lean_del_object(v___x_1238_);
goto v___jp_1258_;
}
else
{
goto v___jp_1261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args){
lean_object* v_ctx_1340_ = _args[0];
lean_object* v_a_1341_ = _args[1];
lean_object* v_as_1342_ = _args[2];
lean_object* v_sz_1343_ = _args[3];
lean_object* v_i_1344_ = _args[4];
lean_object* v_b_1345_ = _args[5];
lean_object* v___y_1346_ = _args[6];
lean_object* v___y_1347_ = _args[7];
lean_object* v___y_1348_ = _args[8];
lean_object* v___y_1349_ = _args[9];
lean_object* v___y_1350_ = _args[10];
lean_object* v___y_1351_ = _args[11];
lean_object* v___y_1352_ = _args[12];
lean_object* v___y_1353_ = _args[13];
lean_object* v___y_1354_ = _args[14];
lean_object* v___y_1355_ = _args[15];
lean_object* v___y_1356_ = _args[16];
_start:
{
uint8_t v_a_162637__boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v_a_162637__boxed_1357_ = lean_unbox(v_a_1341_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1343_);
lean_dec(v_sz_1343_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1340_, v_a_162637__boxed_1357_, v_as_1342_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v_as_1342_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1361_, uint8_t v_a_1362_, lean_object* v_as_1363_, size_t v_sz_1364_, size_t v_i_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1365_, v_sz_1364_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_ctx_1361_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1366_);
return v___x_1379_;
}
else
{
lean_object* v_snd_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1482_; 
v_snd_1380_ = lean_ctor_get(v_b_1366_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_b_1366_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_b_1366_, 0);
lean_dec(v_unused_1483_);
v___x_1382_ = v_b_1366_;
v_isShared_1383_ = v_isSharedCheck_1482_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1380_);
lean_dec(v_b_1366_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1482_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1481_; 
v_fst_1384_ = lean_ctor_get(v_snd_1380_, 0);
v_snd_1385_ = lean_ctor_get(v_snd_1380_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_snd_1380_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1387_ = v_snd_1380_;
v_isShared_1388_ = v_isSharedCheck_1481_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1384_);
lean_dec(v_snd_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1481_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v_a_1391_; lean_object* v_a_1404_; uint8_t v___y_1478_; uint8_t v___x_1479_; 
v___x_1389_ = lean_box(0);
v_a_1404_ = lean_array_uget_borrowed(v_as_1363_, v_i_1365_);
v___x_1479_ = l_Lean_Expr_isApp(v_a_1404_);
if (v___x_1479_ == 0)
{
v___y_1478_ = v_a_1362_;
goto v___jp_1477_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Lean_Expr_isEq(v_a_1404_);
if (v___x_1480_ == 0)
{
goto v___jp_1405_;
}
else
{
v___y_1478_ = v_a_1362_;
goto v___jp_1477_;
}
}
v___jp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_a_1391_);
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_a_1391_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
size_t v___x_1394_; size_t v___x_1395_; 
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1365_, v___x_1394_);
v_i_1365_ = v___x_1395_;
v_b_1366_ = v___x_1393_;
goto _start;
}
}
v___jp_1398_:
{
lean_object* v___x_1400_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v_snd_1385_);
lean_ctor_set(v___x_1382_, 0, v_fst_1384_);
v___x_1400_ = v___x_1382_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_fst_1384_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_snd_1385_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v_a_1391_ = v___x_1400_;
goto v___jp_1390_;
}
}
v___jp_1402_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_fst_1384_);
lean_ctor_set(v___x_1403_, 1, v_snd_1385_);
v_a_1391_ = v___x_1403_;
goto v___jp_1390_;
}
v___jp_1405_:
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Expr_isHEq(v_a_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_inc(v_a_1404_);
v___x_1407_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1404_, v___y_1367_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; uint8_t v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = lean_unbox(v_a_1408_);
lean_dec(v_a_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_del_object(v___x_1382_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_fst_1384_);
lean_ctor_set(v___x_1410_, 1, v_snd_1385_);
v_a_1391_ = v___x_1410_;
goto v___jp_1390_;
}
else
{
lean_object* v_isInterpreted_1411_; lean_object* v___x_1412_; 
v_isInterpreted_1411_ = lean_ctor_get(v_ctx_1361_, 0);
lean_inc_ref(v_isInterpreted_1411_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc(v_a_1404_);
v___x_1412_ = lean_apply_12(v_isInterpreted_1411_, v_a_1404_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, lean_box(0));
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; uint8_t v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = lean_unbox(v_a_1413_);
lean_dec(v_a_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = l_Lean_Expr_getAppFn(v_a_1404_);
lean_inc_ref(v___x_1415_);
v___x_1416_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1415_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = lean_unbox(v_a_1417_);
lean_dec(v_a_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1415_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v_dummy_1421_; lean_object* v_nargs_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; size_t v_sz_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
lean_del_object(v___x_1382_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v_dummy_1421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1422_ = l_Lean_Expr_getAppNumArgs(v_a_1404_);
lean_inc(v_nargs_1422_);
v___x_1423_ = lean_mk_array(v_nargs_1422_, v_dummy_1421_);
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_sub(v_nargs_1422_, v___x_1424_);
lean_dec(v_nargs_1422_);
lean_inc_n(v_a_1404_, 2);
v___x_1426_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1404_, v___x_1423_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_snd_1385_);
lean_ctor_set(v___x_1427_, 1, v___x_1420_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_fst_1384_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v_sz_1429_ = lean_array_size(v___x_1426_);
v___x_1430_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1361_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1404_, v_ctx_1361_, v___x_1415_, v___x_1426_, v_sz_1429_, v___x_1430_, v___x_1428_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec_ref(v___x_1426_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v_snd_1433_; lean_object* v_fst_1434_; lean_object* v_fst_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v_snd_1433_ = lean_ctor_get(v_a_1432_, 1);
lean_inc(v_snd_1433_);
v_fst_1434_ = lean_ctor_get(v_a_1432_, 0);
lean_inc(v_fst_1434_);
lean_dec(v_a_1432_);
v_fst_1435_ = lean_ctor_get(v_snd_1433_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_snd_1433_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_snd_1433_, 1);
lean_dec(v_unused_1443_);
v___x_1437_ = v_snd_1433_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_fst_1435_);
lean_dec(v_snd_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_fst_1435_);
lean_ctor_set(v___x_1437_, 0, v_fst_1434_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_fst_1434_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_fst_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_a_1391_ = v___x_1440_;
goto v___jp_1390_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_del_object(v___x_1387_);
lean_dec_ref(v_ctx_1361_);
v_a_1444_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1431_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1431_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_dec_ref(v___x_1415_);
goto v___jp_1398_;
}
}
else
{
lean_dec_ref(v___x_1415_);
goto v___jp_1398_;
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v___x_1415_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec_ref(v_ctx_1361_);
v_a_1452_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1416_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1416_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v___x_1460_; 
lean_del_object(v___x_1382_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_fst_1384_);
lean_ctor_set(v___x_1460_, 1, v_snd_1385_);
v_a_1391_ = v___x_1460_;
goto v___jp_1390_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec_ref(v_ctx_1361_);
v_a_1461_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1412_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1412_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec_ref(v_ctx_1361_);
v_a_1469_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1407_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1407_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_del_object(v___x_1382_);
goto v___jp_1402_;
}
}
v___jp_1477_:
{
if (v___y_1478_ == 0)
{
lean_del_object(v___x_1382_);
goto v___jp_1402_;
}
else
{
goto v___jp_1405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object** _args){
lean_object* v_ctx_1484_ = _args[0];
lean_object* v_a_1485_ = _args[1];
lean_object* v_as_1486_ = _args[2];
lean_object* v_sz_1487_ = _args[3];
lean_object* v_i_1488_ = _args[4];
lean_object* v_b_1489_ = _args[5];
lean_object* v___y_1490_ = _args[6];
lean_object* v___y_1491_ = _args[7];
lean_object* v___y_1492_ = _args[8];
lean_object* v___y_1493_ = _args[9];
lean_object* v___y_1494_ = _args[10];
lean_object* v___y_1495_ = _args[11];
lean_object* v___y_1496_ = _args[12];
lean_object* v___y_1497_ = _args[13];
lean_object* v___y_1498_ = _args[14];
lean_object* v___y_1499_ = _args[15];
lean_object* v___y_1500_ = _args[16];
_start:
{
uint8_t v_a_162865__boxed_1501_; size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_a_162865__boxed_1501_ = lean_unbox(v_a_1485_);
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1487_);
lean_dec(v_sz_1487_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1484_, v_a_162865__boxed_1501_, v_as_1486_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v_as_1486_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1505_, uint8_t v_a_1506_, lean_object* v_as_1507_, size_t v_sz_1508_, size_t v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1509_, v_sz_1508_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec_ref(v_ctx_1505_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1510_);
return v___x_1523_;
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1626_; 
v_snd_1524_ = lean_ctor_get(v_b_1510_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_b_1510_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v_b_1510_, 0);
lean_dec(v_unused_1627_);
v___x_1526_ = v_b_1510_;
v_isShared_1527_ = v_isSharedCheck_1626_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_b_1510_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1626_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_fst_1528_; lean_object* v_snd_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1625_; 
v_fst_1528_ = lean_ctor_get(v_snd_1524_, 0);
v_snd_1529_ = lean_ctor_get(v_snd_1524_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_snd_1524_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1531_ = v_snd_1524_;
v_isShared_1532_ = v_isSharedCheck_1625_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_snd_1529_);
lean_inc(v_fst_1528_);
lean_dec(v_snd_1524_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1625_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v_a_1535_; lean_object* v_a_1548_; uint8_t v___y_1622_; uint8_t v___x_1623_; 
v___x_1533_ = lean_box(0);
v_a_1548_ = lean_array_uget_borrowed(v_as_1507_, v_i_1509_);
v___x_1623_ = l_Lean_Expr_isApp(v_a_1548_);
if (v___x_1623_ == 0)
{
v___y_1622_ = v_a_1506_;
goto v___jp_1621_;
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = l_Lean_Expr_isEq(v_a_1548_);
if (v___x_1624_ == 0)
{
goto v___jp_1549_;
}
else
{
v___y_1622_ = v_a_1506_;
goto v___jp_1621_;
}
}
v___jp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v_a_1535_);
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1537_ = v___x_1531_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1535_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1509_, v___x_1538_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1505_, v_a_1506_, v_as_1507_, v_sz_1508_, v___x_1539_, v___x_1537_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1540_;
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_snd_1529_);
lean_ctor_set(v___x_1526_, 0, v_fst_1528_);
v___x_1544_ = v___x_1526_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_snd_1529_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v_a_1535_ = v___x_1544_;
goto v___jp_1534_;
}
}
v___jp_1546_:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_fst_1528_);
lean_ctor_set(v___x_1547_, 1, v_snd_1529_);
v_a_1535_ = v___x_1547_;
goto v___jp_1534_;
}
v___jp_1549_:
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_Expr_isHEq(v_a_1548_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_inc(v_a_1548_);
v___x_1551_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1548_, v___y_1511_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; uint8_t v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_unbox(v_a_1552_);
lean_dec(v_a_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_del_object(v___x_1526_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_fst_1528_);
lean_ctor_set(v___x_1554_, 1, v_snd_1529_);
v_a_1535_ = v___x_1554_;
goto v___jp_1534_;
}
else
{
lean_object* v_isInterpreted_1555_; lean_object* v___x_1556_; 
v_isInterpreted_1555_ = lean_ctor_get(v_ctx_1505_, 0);
lean_inc_ref(v_isInterpreted_1555_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
lean_inc(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v_a_1548_);
v___x_1556_ = lean_apply_12(v_isInterpreted_1555_, v_a_1548_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, lean_box(0));
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; uint8_t v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_unbox(v_a_1557_);
lean_dec(v_a_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_Expr_getAppFn(v_a_1548_);
lean_inc_ref(v___x_1559_);
v___x_1560_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1559_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = lean_unbox(v_a_1561_);
lean_dec(v_a_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1559_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v_dummy_1565_; lean_object* v_nargs_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1526_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v_dummy_1565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1566_ = l_Lean_Expr_getAppNumArgs(v_a_1548_);
lean_inc(v_nargs_1566_);
v___x_1567_ = lean_mk_array(v_nargs_1566_, v_dummy_1565_);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_sub(v_nargs_1566_, v___x_1568_);
lean_dec(v_nargs_1566_);
lean_inc_n(v_a_1548_, 2);
v___x_1570_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1548_, v___x_1567_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_snd_1529_);
lean_ctor_set(v___x_1571_, 1, v___x_1564_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_fst_1528_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v_sz_1573_ = lean_array_size(v___x_1570_);
v___x_1574_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1505_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1548_, v_ctx_1505_, v___x_1559_, v___x_1570_, v_sz_1573_, v___x_1574_, v___x_1572_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec_ref(v___x_1570_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_snd_1577_; lean_object* v_fst_1578_; lean_object* v_fst_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_snd_1577_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_snd_1577_);
v_fst_1578_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_fst_1578_);
lean_dec(v_a_1576_);
v_fst_1579_ = lean_ctor_get(v_snd_1577_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_snd_1577_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_snd_1577_, 1);
lean_dec(v_unused_1587_);
v___x_1581_ = v_snd_1577_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_fst_1579_);
lean_dec(v_snd_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v_fst_1579_);
lean_ctor_set(v___x_1581_, 0, v_fst_1578_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_fst_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_fst_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
v_a_1535_ = v___x_1584_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_del_object(v___x_1531_);
lean_dec_ref(v_ctx_1505_);
v_a_1588_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1575_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1575_);
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
else
{
lean_dec_ref(v___x_1559_);
goto v___jp_1542_;
}
}
else
{
lean_dec_ref(v___x_1559_);
goto v___jp_1542_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___x_1559_);
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_del_object(v___x_1526_);
lean_dec_ref(v_ctx_1505_);
v_a_1596_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1560_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1560_);
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
lean_object* v___x_1604_; 
lean_del_object(v___x_1526_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_fst_1528_);
lean_ctor_set(v___x_1604_, 1, v_snd_1529_);
v_a_1535_ = v___x_1604_;
goto v___jp_1534_;
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_del_object(v___x_1526_);
lean_dec_ref(v_ctx_1505_);
v_a_1605_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1556_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1556_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_del_object(v___x_1526_);
lean_dec_ref(v_ctx_1505_);
v_a_1613_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1551_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1551_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_del_object(v___x_1526_);
goto v___jp_1546_;
}
}
v___jp_1621_:
{
if (v___y_1622_ == 0)
{
lean_del_object(v___x_1526_);
goto v___jp_1546_;
}
else
{
goto v___jp_1549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object** _args){
lean_object* v_ctx_1628_ = _args[0];
lean_object* v_a_1629_ = _args[1];
lean_object* v_as_1630_ = _args[2];
lean_object* v_sz_1631_ = _args[3];
lean_object* v_i_1632_ = _args[4];
lean_object* v_b_1633_ = _args[5];
lean_object* v___y_1634_ = _args[6];
lean_object* v___y_1635_ = _args[7];
lean_object* v___y_1636_ = _args[8];
lean_object* v___y_1637_ = _args[9];
lean_object* v___y_1638_ = _args[10];
lean_object* v___y_1639_ = _args[11];
lean_object* v___y_1640_ = _args[12];
lean_object* v___y_1641_ = _args[13];
lean_object* v___y_1642_ = _args[14];
lean_object* v___y_1643_ = _args[15];
lean_object* v___y_1644_ = _args[16];
_start:
{
uint8_t v_a_163093__boxed_1645_; size_t v_sz_boxed_1646_; size_t v_i_boxed_1647_; lean_object* v_res_1648_; 
v_a_163093__boxed_1645_ = lean_unbox(v_a_1629_);
v_sz_boxed_1646_ = lean_unbox_usize(v_sz_1631_);
lean_dec(v_sz_1631_);
v_i_boxed_1647_ = lean_unbox_usize(v_i_1632_);
lean_dec(v_i_1632_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1628_, v_a_163093__boxed_1645_, v_as_1630_, v_sz_boxed_1646_, v_i_boxed_1647_, v_b_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v_as_1630_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1649_, lean_object* v_ctx_1650_, uint8_t v_a_1651_, lean_object* v_n_1652_, lean_object* v_b_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
if (lean_obj_tag(v_n_1652_) == 0)
{
lean_object* v_cs_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; size_t v_sz_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v_cs_1665_ = lean_ctor_get(v_n_1652_, 0);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_b_1653_);
v_sz_1668_ = lean_array_size(v_cs_1665_);
v___x_1669_ = ((size_t)0ULL);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1649_, v_ctx_1650_, v_a_1651_, v_cs_1665_, v_sz_1668_, v___x_1669_, v___x_1667_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1685_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_fst_1675_; 
v_fst_1675_ = lean_ctor_get(v_a_1671_, 0);
if (lean_obj_tag(v_fst_1675_) == 0)
{
lean_object* v_snd_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v_snd_1676_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1676_);
lean_dec(v_a_1671_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_snd_1676_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; 
lean_inc_ref(v_fst_1675_);
lean_dec(v_a_1671_);
v_val_1681_ = lean_ctor_get(v_fst_1675_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_fst_1675_, 1);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_val_1681_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_val_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1670_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1670_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_vs_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_vs_1694_ = lean_ctor_get(v_n_1652_, 0);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_b_1653_);
v_sz_1697_ = lean_array_size(v_vs_1694_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1650_, v_a_1651_, v_vs_1694_, v_sz_1697_, v___x_1698_, v___x_1696_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1714_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_fst_1704_; 
v_fst_1704_ = lean_ctor_get(v_a_1700_, 0);
if (lean_obj_tag(v_fst_1704_) == 0)
{
lean_object* v_snd_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v_snd_1705_ = lean_ctor_get(v_a_1700_, 1);
lean_inc(v_snd_1705_);
lean_dec(v_a_1700_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_snd_1705_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1712_; 
lean_inc_ref(v_fst_1704_);
lean_dec(v_a_1700_);
v_val_1710_ = lean_ctor_get(v_fst_1704_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_fst_1704_, 1);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_val_1710_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_val_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1699_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1699_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1723_, lean_object* v_ctx_1724_, uint8_t v_a_1725_, lean_object* v_as_1726_, size_t v_sz_1727_, size_t v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_lt(v_i_1728_, v_sz_1727_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v_ctx_1724_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1729_);
return v___x_1742_;
}
else
{
lean_object* v_snd_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1777_; 
v_snd_1743_ = lean_ctor_get(v_b_1729_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_b_1729_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v_b_1729_, 0);
lean_dec(v_unused_1778_);
v___x_1745_ = v_b_1729_;
v_isShared_1746_ = v_isSharedCheck_1777_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snd_1743_);
lean_dec(v_b_1729_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1777_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v_a_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_box(0);
v_a_1748_ = lean_array_uget_borrowed(v_as_1726_, v_i_1728_);
lean_inc(v_snd_1743_);
lean_inc_ref(v_ctx_1724_);
v___x_1749_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1723_, v_ctx_1724_, v_a_1725_, v_a_1748_, v_snd_1743_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1768_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1768_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1768_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
if (lean_obj_tag(v_a_1750_) == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec_ref(v_ctx_1724_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_a_1750_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1754_);
v___x_1756_ = v___x_1745_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_snd_1743_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1756_);
v___x_1758_ = v___x_1752_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; 
lean_del_object(v___x_1752_);
lean_dec(v_snd_1743_);
v_a_1761_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v_a_1750_, 1);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_a_1761_);
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1763_ = v___x_1745_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_a_1761_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
size_t v___x_1764_; size_t v___x_1765_; 
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1728_, v___x_1764_);
v_i_1728_ = v___x_1765_;
v_b_1729_ = v___x_1763_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1745_);
lean_dec(v_snd_1743_);
lean_dec_ref(v_ctx_1724_);
v_a_1769_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1749_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1749_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1779_ = _args[0];
lean_object* v_ctx_1780_ = _args[1];
lean_object* v_a_1781_ = _args[2];
lean_object* v_as_1782_ = _args[3];
lean_object* v_sz_1783_ = _args[4];
lean_object* v_i_1784_ = _args[5];
lean_object* v_b_1785_ = _args[6];
lean_object* v___y_1786_ = _args[7];
lean_object* v___y_1787_ = _args[8];
lean_object* v___y_1788_ = _args[9];
lean_object* v___y_1789_ = _args[10];
lean_object* v___y_1790_ = _args[11];
lean_object* v___y_1791_ = _args[12];
lean_object* v___y_1792_ = _args[13];
lean_object* v___y_1793_ = _args[14];
lean_object* v___y_1794_ = _args[15];
lean_object* v___y_1795_ = _args[16];
lean_object* v___y_1796_ = _args[17];
_start:
{
uint8_t v_a_163320__boxed_1797_; size_t v_sz_boxed_1798_; size_t v_i_boxed_1799_; lean_object* v_res_1800_; 
v_a_163320__boxed_1797_ = lean_unbox(v_a_1781_);
v_sz_boxed_1798_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1779_, v_ctx_1780_, v_a_163320__boxed_1797_, v_as_1782_, v_sz_boxed_1798_, v_i_boxed_1799_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v_as_1782_);
lean_dec_ref(v_init_1779_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1801_, lean_object* v_ctx_1802_, lean_object* v_a_1803_, lean_object* v_n_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_a_163348__boxed_1817_; lean_object* v_res_1818_; 
v_a_163348__boxed_1817_ = lean_unbox(v_a_1803_);
v_res_1818_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1801_, v_ctx_1802_, v_a_163348__boxed_1817_, v_n_1804_, v_b_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v_n_1804_);
lean_dec_ref(v_init_1801_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1819_, uint8_t v_a_1820_, lean_object* v_t_1821_, lean_object* v_init_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_root_1834_; lean_object* v_tail_1835_; lean_object* v___x_1836_; 
v_root_1834_ = lean_ctor_get(v_t_1821_, 0);
v_tail_1835_ = lean_ctor_get(v_t_1821_, 1);
lean_inc_ref(v_ctx_1819_);
lean_inc_ref(v_init_1822_);
v___x_1836_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1822_, v_ctx_1819_, v_a_1820_, v_root_1834_, v_init_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_init_1822_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1873_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1873_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1873_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v_ctx_1819_);
v_a_1841_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v_a_1837_, 1);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_a_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1839_);
v_a_1845_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v_a_1837_, 1);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v_a_1845_);
v_sz_1848_ = lean_array_size(v_tail_1835_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1819_, v_a_1820_, v_tail_1835_, v_sz_1848_, v___x_1849_, v___x_1847_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1864_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_fst_1855_; 
v_fst_1855_ = lean_ctor_get(v_a_1851_, 0);
if (lean_obj_tag(v_fst_1855_) == 0)
{
lean_object* v_snd_1856_; lean_object* v___x_1858_; 
v_snd_1856_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_snd_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_snd_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v_val_1860_; lean_object* v___x_1862_; 
lean_inc_ref(v_fst_1855_);
lean_dec(v_a_1851_);
v_val_1860_ = lean_ctor_get(v_fst_1855_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v_fst_1855_, 1);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_val_1860_);
v___x_1862_ = v___x_1853_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_val_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1850_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1850_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_ctx_1819_);
v_a_1874_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1836_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1836_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1882_, lean_object* v_a_1883_, lean_object* v_t_1884_, lean_object* v_init_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v_a_163569__boxed_1897_; lean_object* v_res_1898_; 
v_a_163569__boxed_1897_ = lean_unbox(v_a_1883_);
v_res_1898_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1882_, v_a_163569__boxed_1897_, v_t_1884_, v_init_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v_t_1884_);
return v_res_1898_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1904_ = l_Lean_Name_append(v___x_1903_, v___x_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1905_, size_t v_i_1906_, size_t v_stop_1907_, lean_object* v_b_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_a_1921_; uint8_t v___x_1925_; 
v___x_1925_ = lean_usize_dec_eq(v_i_1906_, v_stop_1907_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_array_uget_borrowed(v_as_1905_, v_i_1906_);
v___x_1927_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1926_, v___y_1909_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; uint8_t v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
if (v___x_1929_ == 0)
{
if (lean_obj_tag(v___x_1926_) == 2)
{
lean_object* v_a_1930_; lean_object* v_b_1931_; lean_object* v_eq_1932_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v_toCold_1988_; lean_object* v_options_1989_; uint8_t v_hasTrace_1990_; 
v_a_1930_ = lean_ctor_get(v___x_1926_, 0);
v_b_1931_ = lean_ctor_get(v___x_1926_, 1);
v_eq_1932_ = lean_ctor_get(v___x_1926_, 3);
v_toCold_1988_ = lean_ctor_get(v___y_1917_, 0);
v_options_1989_ = lean_ctor_get(v_toCold_1988_, 2);
v_hasTrace_1990_ = lean_ctor_get_uint8(v_options_1989_, sizeof(void*)*1);
if (v_hasTrace_1990_ == 0)
{
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
goto v___jp_1956_;
}
else
{
lean_object* v_inheritedTraceOptions_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_inheritedTraceOptions_1991_ = lean_ctor_get(v_toCold_1988_, 11);
v___x_1992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1993_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1991_, v_options_1989_, v___x_1993_);
if (v___x_1994_ == 0)
{
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v_eq_1932_);
v___x_1995_ = l_Lean_MessageData_ofExpr(v_eq_1932_);
v___x_1996_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1992_, v___x_1995_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref_known(v___x_1996_, 1);
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
goto v___jp_1956_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_b_1908_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
v___jp_1933_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_box(0);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1940_);
lean_inc(v___y_1941_);
lean_inc(v___y_1936_);
lean_inc_ref(v_eq_1932_);
v___x_1946_ = lean_grind_internalize(v_eq_1932_, v___y_1944_, v___x_1945_, v___y_1936_, v___y_1941_, v___y_1940_, v___y_1937_, v___y_1935_, v___y_1939_, v___y_1934_, v___y_1942_, v___y_1943_, v___y_1938_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref_known(v___x_1946_, 1);
lean_inc_ref(v___x_1926_);
v___x_1947_ = lean_array_push(v_b_1908_, v___x_1926_);
v_a_1921_ = v___x_1947_;
goto v___jp_1920_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_b_1908_);
v_a_1948_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1930_, v___y_1957_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1931_, v___y_1957_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; uint8_t v___x_1971_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = lean_nat_dec_le(v_a_1968_, v_a_1970_);
if (v___x_1971_ == 0)
{
lean_dec(v_a_1970_);
v___y_1934_ = v___y_1963_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v___y_1957_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1962_;
v___y_1940_ = v___y_1959_;
v___y_1941_ = v___y_1958_;
v___y_1942_ = v___y_1964_;
v___y_1943_ = v___y_1965_;
v___y_1944_ = v_a_1968_;
goto v___jp_1933_;
}
else
{
lean_dec(v_a_1968_);
v___y_1934_ = v___y_1963_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v___y_1957_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1962_;
v___y_1940_ = v___y_1959_;
v___y_1941_ = v___y_1958_;
v___y_1942_ = v___y_1964_;
v___y_1943_ = v___y_1965_;
v___y_1944_ = v_a_1970_;
goto v___jp_1933_;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_a_1968_);
lean_dec_ref(v_b_1908_);
v_a_1972_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1969_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1969_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_b_1908_);
v_a_1980_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1967_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1967_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
else
{
v_a_1921_ = v_b_1908_;
goto v___jp_1920_;
}
}
else
{
v_a_1921_ = v_b_1908_;
goto v___jp_1920_;
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_b_1908_);
v_a_2005_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1927_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1927_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_1908_);
return v___x_2013_;
}
v___jp_1920_:
{
size_t v___x_1922_; size_t v___x_1923_; 
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_add(v_i_1906_, v___x_1922_);
v_i_1906_ = v___x_1923_;
v_b_1908_ = v_a_1921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_2014_, lean_object* v_i_2015_, lean_object* v_stop_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_i_boxed_2029_; size_t v_stop_boxed_2030_; lean_object* v_res_2031_; 
v_i_boxed_2029_ = lean_unbox_usize(v_i_2015_);
lean_dec(v_i_2015_);
v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2016_);
lean_dec(v_stop_2016_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2014_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v_as_2014_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2034_, lean_object* v_start_2035_, lean_object* v_stop_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2049_ = lean_nat_dec_lt(v_start_2035_, v_stop_2036_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = lean_array_get_size(v_as_2034_);
v___x_2052_ = lean_nat_dec_le(v_stop_2036_, v___x_2051_);
if (v___x_2052_ == 0)
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_nat_dec_lt(v_start_2035_, v___x_2051_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2048_);
return v___x_2054_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = lean_usize_of_nat(v_start_2035_);
v___x_2056_ = lean_usize_of_nat(v___x_2051_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2034_, v___x_2055_, v___x_2056_, v___x_2048_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2057_;
}
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_usize_of_nat(v_start_2035_);
v___x_2059_ = lean_usize_of_nat(v_stop_2036_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2034_, v___x_2058_, v___x_2059_, v___x_2048_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2061_, lean_object* v_start_2062_, lean_object* v_stop_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2061_, v_start_2062_, v_stop_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec(v_stop_2063_);
lean_dec(v_start_2062_);
lean_dec_ref(v_as_2061_);
return v_res_2075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_unsigned_to_nat(16u);
v___x_2078_ = lean_mk_array(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2093_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2304_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2304_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2304_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
uint8_t v_mbtc_2107_; 
v_mbtc_2107_ = lean_ctor_get_uint8(v_a_2103_, sizeof(void*)*14 + 18);
lean_dec(v_a_2103_);
if (v_mbtc_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_dec_ref(v_ctx_2090_);
v___x_2108_ = lean_box(v_mbtc_2107_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_object* v___x_2112_; 
lean_del_object(v___x_2105_);
v___x_2112_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2091_, v_a_2093_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2303_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2303_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2303_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_unbox(v_a_2113_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_toGoalState_2120_; lean_object* v_exprs_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2115_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_st_ref_get(v_a_2091_);
v_toGoalState_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_ref(v_toGoalState_2120_);
lean_dec(v___x_2119_);
v_exprs_2121_ = lean_ctor_get(v_toGoalState_2120_, 2);
lean_inc_ref(v_exprs_2121_);
lean_dec_ref(v_toGoalState_2120_);
v___x_2122_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2123_ = lean_unbox(v_a_2113_);
v___x_2124_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2090_, v___x_2123_, v_exprs_2121_, v___x_2122_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec_ref(v_exprs_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2289_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2289_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2289_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_snd_2129_; lean_object* v_size_2130_; lean_object* v_buckets_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2288_; 
v_snd_2129_ = lean_ctor_get(v_a_2125_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2125_);
v_size_2130_ = lean_ctor_get(v_snd_2129_, 0);
v_buckets_2131_ = lean_ctor_get(v_snd_2129_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_snd_2129_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2133_ = v_snd_2129_;
v_isShared_2134_ = v_isSharedCheck_2288_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_buckets_2131_);
lean_inc(v_size_2130_);
lean_dec(v_snd_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2288_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_eq(v_size_2130_, v___x_2118_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_del_object(v___x_2127_);
lean_dec(v_a_2113_);
v___x_2136_ = lean_st_ref_get(v_a_2091_);
v___x_2137_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2093_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_toGoalState_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2275_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_toGoalState_2139_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; 
v_unused_2276_ = lean_ctor_get(v___x_2136_, 1);
lean_dec(v_unused_2276_);
v___x_2141_ = v___x_2136_;
v_isShared_2142_ = v_isSharedCheck_2275_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_toGoalState_2139_);
lean_dec(v___x_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2275_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_split_2143_; lean_object* v_splits_2144_; lean_object* v_num_2145_; uint8_t v___x_2146_; lean_object* v___y_2148_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2204_; 
v_split_2143_ = lean_ctor_get(v_toGoalState_2139_, 14);
lean_inc_ref(v_split_2143_);
lean_dec_ref(v_toGoalState_2139_);
v_splits_2144_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_splits_2144_);
lean_dec(v_a_2138_);
v_num_2145_ = lean_ctor_get(v_split_2143_, 0);
lean_inc(v_num_2145_);
lean_dec_ref(v_split_2143_);
v___x_2146_ = lean_nat_dec_lt(v_splits_2144_, v_num_2145_);
lean_dec(v_num_2145_);
lean_dec(v_splits_2144_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
lean_del_object(v___x_2141_);
lean_del_object(v___x_2133_);
v___x_2210_ = lean_mk_empty_array_with_capacity(v_size_2130_);
lean_dec(v_size_2130_);
v___x_2211_ = lean_array_get_size(v_buckets_2131_);
v___x_2212_ = lean_nat_dec_lt(v___x_2118_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_dec_ref(v_buckets_2131_);
v___y_2204_ = v___x_2210_;
goto v___jp_2203_;
}
else
{
size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = lean_usize_of_nat(v___x_2211_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2131_, v___x_2213_, v___x_2214_, v___x_2210_);
lean_dec_ref(v_buckets_2131_);
v___y_2204_ = v___x_2215_;
goto v___jp_2203_;
}
}
else
{
lean_object* v___x_2216_; 
lean_dec_ref(v_buckets_2131_);
lean_dec(v_size_2130_);
v___x_2216_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2093_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_splits_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_splits_2218_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_splits_2218_);
lean_dec(v_a_2217_);
v___x_2219_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2220_ = l_Nat_reprFast(v_splits_2218_);
v___x_2221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = l_Lean_MessageData_ofFormat(v___x_2221_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 7);
lean_ctor_set(v___x_2141_, 1, v___x_2222_);
lean_ctor_set(v___x_2141_, 0, v___x_2219_);
v___x_2224_ = v___x_2141_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 7);
lean_ctor_set(v___x_2133_, 1, v___x_2225_);
lean_ctor_set(v___x_2133_, 0, v___x_2224_);
v___x_2227_ = v___x_2133_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2095_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2256_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2256_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2256_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
uint8_t v_verbose_2233_; 
v_verbose_2233_ = lean_ctor_get_uint8(v_a_2229_, 0);
lean_dec(v_a_2229_);
if (v_verbose_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec_ref(v___x_2227_);
v___x_2234_ = lean_box(v___x_2135_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v___x_2238_; 
lean_del_object(v___x_2231_);
v___x_2238_ = l_Lean_Meta_Sym_reportIssue(v___x_2227_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2238_, 0);
lean_dec(v_unused_2247_);
v___x_2240_ = v___x_2238_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v___x_2238_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_box(v___x_2135_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2238_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2238_);
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
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v___x_2227_);
v_a_2257_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2228_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2228_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2141_);
lean_del_object(v___x_2133_);
v_a_2267_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2216_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2216_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
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
v___jp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_array_get_size(v___y_2148_);
v___x_2150_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2148_, v___x_2118_, v___x_2149_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec_ref(v___y_2148_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2182_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2182_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2182_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_array_get_size(v_a_2151_);
v___x_2156_ = lean_nat_dec_eq(v___x_2155_, v___x_2118_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; size_t v_sz_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
lean_del_object(v___x_2153_);
v___x_2157_ = lean_box(0);
v_sz_2158_ = lean_array_size(v_a_2151_);
v___x_2159_ = ((size_t)0ULL);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2151_, v_sz_2158_, v___x_2159_, v___x_2157_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2151_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2169_);
v___x_2162_ = v___x_2160_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v___x_2160_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_box(v_mbtc_2107_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2160_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2160_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v_a_2151_);
v___x_2178_ = lean_box(v___x_2146_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2178_);
v___x_2180_ = v___x_2153_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2150_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2150_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
v___jp_2191_:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2193_, v___y_2192_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec(v___y_2193_);
v___y_2148_ = v___x_2196_;
goto v___jp_2147_;
}
v___jp_2197_:
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_nat_dec_le(v___y_2201_, v___y_2200_);
if (v___x_2202_ == 0)
{
lean_dec(v___y_2200_);
lean_inc(v___y_2201_);
v___y_2192_ = v___y_2198_;
v___y_2193_ = v___y_2199_;
v___y_2194_ = v___y_2201_;
v___y_2195_ = v___y_2201_;
goto v___jp_2191_;
}
else
{
v___y_2192_ = v___y_2198_;
v___y_2193_ = v___y_2199_;
v___y_2194_ = v___y_2201_;
v___y_2195_ = v___y_2200_;
goto v___jp_2191_;
}
}
v___jp_2203_:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_array_get_size(v___y_2204_);
v___x_2206_ = lean_nat_dec_eq(v___x_2205_, v___x_2118_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v___x_2205_, v___x_2207_);
v___x_2209_ = lean_nat_dec_le(v___x_2118_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_inc(v___x_2208_);
v___y_2198_ = v___y_2204_;
v___y_2199_ = v___x_2205_;
v___y_2200_ = v___x_2208_;
v___y_2201_ = v___x_2208_;
goto v___jp_2197_;
}
else
{
v___y_2198_ = v___y_2204_;
v___y_2199_ = v___x_2205_;
v___y_2200_ = v___x_2208_;
v___y_2201_ = v___x_2118_;
goto v___jp_2197_;
}
}
else
{
v___y_2148_ = v___y_2204_;
goto v___jp_2147_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v___x_2136_);
lean_del_object(v___x_2133_);
lean_dec_ref(v_buckets_2131_);
lean_dec(v_size_2130_);
v_a_2277_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2137_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2137_);
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
else
{
lean_object* v___x_2286_; 
lean_del_object(v___x_2133_);
lean_dec_ref(v_buckets_2131_);
lean_dec(v_size_2130_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v_a_2113_);
v___x_2286_ = v___x_2127_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2113_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2113_);
v_a_2290_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2124_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2124_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_ctx_2090_);
v___x_2298_ = 0;
v___x_2299_ = lean_box(v___x_2298_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2299_);
v___x_2301_ = v___x_2115_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2090_);
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_ctx_2090_);
v_a_2305_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2102_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2102_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Meta_Grind_mbtc(v_ctx_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec(v_a_2314_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2326_, lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2326_, v_msg_2327_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2340_, lean_object* v_msg_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2340_, v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2354_, lean_object* v_m_2355_, lean_object* v_a_2356_, lean_object* v_b_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2355_, v_a_2356_, v_b_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2359_, lean_object* v_m_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2360_, v_a_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_m_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2363_, v_m_2364_, v_a_2365_);
lean_dec_ref(v_a_2365_);
lean_dec_ref(v_m_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2367_, lean_object* v_val_2368_, lean_object* v___x_2369_, lean_object* v___x_2370_, lean_object* v_as_2371_, lean_object* v_as_x27_2372_, lean_object* v_b_2373_, lean_object* v_a_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2367_, v_val_2368_, v___x_2369_, v___x_2370_, v_as_x27_2372_, v_b_2373_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2387_ = _args[0];
lean_object* v_val_2388_ = _args[1];
lean_object* v___x_2389_ = _args[2];
lean_object* v___x_2390_ = _args[3];
lean_object* v_as_2391_ = _args[4];
lean_object* v_as_x27_2392_ = _args[5];
lean_object* v_b_2393_ = _args[6];
lean_object* v_a_2394_ = _args[7];
lean_object* v___y_2395_ = _args[8];
lean_object* v___y_2396_ = _args[9];
lean_object* v___y_2397_ = _args[10];
lean_object* v___y_2398_ = _args[11];
lean_object* v___y_2399_ = _args[12];
lean_object* v___y_2400_ = _args[13];
lean_object* v___y_2401_ = _args[14];
lean_object* v___y_2402_ = _args[15];
lean_object* v___y_2403_ = _args[16];
lean_object* v___y_2404_ = _args[17];
lean_object* v___y_2405_ = _args[18];
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2387_, v_val_2388_, v___x_2389_, v___x_2390_, v_as_2391_, v_as_x27_2392_, v_b_2393_, v_a_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec(v_as_x27_2392_);
lean_dec(v_as_2391_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2407_, lean_object* v_m_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2408_, v_a_2409_, v_b_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2412_, lean_object* v_as_2413_, lean_object* v_lo_2414_, lean_object* v_hi_2415_, lean_object* v_w_2416_, lean_object* v_hlo_2417_, lean_object* v_hhi_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2412_, v_as_2413_, v_lo_2414_, v_hi_2415_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2420_, lean_object* v_as_2421_, lean_object* v_lo_2422_, lean_object* v_hi_2423_, lean_object* v_w_2424_, lean_object* v_hlo_2425_, lean_object* v_hhi_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2420_, v_as_2421_, v_lo_2422_, v_hi_2423_, v_w_2424_, v_hlo_2425_, v_hhi_2426_);
lean_dec(v_hi_2423_);
lean_dec(v_n_2420_);
return v_res_2427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2428_, lean_object* v_a_2429_, lean_object* v_x_2430_){
_start:
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2429_, v_x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2432_, lean_object* v_a_2433_, lean_object* v_x_2434_){
_start:
{
uint8_t v_res_2435_; lean_object* v_r_2436_; 
v_res_2435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2432_, v_a_2433_, v_x_2434_);
lean_dec(v_x_2434_);
lean_dec_ref(v_a_2433_);
v_r_2436_ = lean_box(v_res_2435_);
return v_r_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2437_, lean_object* v_data_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2440_, lean_object* v_a_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2444_, lean_object* v_a_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2444_, v_a_2445_, v_x_2446_);
lean_dec(v_x_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2448_, lean_object* v_a_2449_, lean_object* v_x_2450_){
_start:
{
uint8_t v___x_2451_; 
v___x_2451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2449_, v_x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2452_, lean_object* v_a_2453_, lean_object* v_x_2454_){
_start:
{
uint8_t v_res_2455_; lean_object* v_r_2456_; 
v_res_2455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2452_, v_a_2453_, v_x_2454_);
lean_dec(v_x_2454_);
lean_dec_ref(v_a_2453_);
v_r_2456_ = lean_box(v_res_2455_);
return v_r_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2457_, lean_object* v_data_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2460_, lean_object* v_a_2461_, lean_object* v_b_2462_, lean_object* v_x_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2461_, v_b_2462_, v_x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2465_, lean_object* v_lo_2466_, lean_object* v_hi_2467_, lean_object* v_hhi_2468_, lean_object* v_pivot_2469_, lean_object* v_as_2470_, lean_object* v_i_2471_, lean_object* v_k_2472_, lean_object* v_ilo_2473_, lean_object* v_ik_2474_, lean_object* v_w_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2467_, v_pivot_2469_, v_as_2470_, v_i_2471_, v_k_2472_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2477_, lean_object* v_lo_2478_, lean_object* v_hi_2479_, lean_object* v_hhi_2480_, lean_object* v_pivot_2481_, lean_object* v_as_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_, lean_object* v_ilo_2485_, lean_object* v_ik_2486_, lean_object* v_w_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2477_, v_lo_2478_, v_hi_2479_, v_hhi_2480_, v_pivot_2481_, v_as_2482_, v_i_2483_, v_k_2484_, v_ilo_2485_, v_ik_2486_, v_w_2487_);
lean_dec_ref(v_pivot_2481_);
lean_dec(v_hi_2479_);
lean_dec(v_lo_2478_);
lean_dec(v_n_2477_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2489_, lean_object* v_i_2490_, lean_object* v_source_2491_, lean_object* v_target_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2490_, v_source_2491_, v_target_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2494_, lean_object* v_i_2495_, lean_object* v_source_2496_, lean_object* v_target_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2495_, v_source_2496_, v_target_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2500_, v_x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2504_, v_x_2505_);
return v___x_2506_;
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
