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
lean_dec_ref_known(v___x_697_, 1);
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
lean_dec_ref_known(v___x_701_, 1);
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
lean_dec_ref_known(v___x_705_, 1);
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
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v_arg_882_; size_t v___x_883_; size_t v___x_884_; uint8_t v___x_885_; 
v_head_880_ = lean_ctor_get(v_x_878_, 0);
v_tail_881_ = lean_ctor_get(v_x_878_, 1);
v_arg_882_ = lean_ctor_get(v_head_880_, 0);
v___x_883_ = lean_ptr_addr(v_val_877_);
v___x_884_ = lean_ptr_addr(v_arg_882_);
v___x_885_ = lean_usize_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_val_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_903_ = l_Lean_Name_append(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_910_, lean_object* v_ctx_911_, lean_object* v___x_912_, lean_object* v_as_913_, size_t v_sz_914_, size_t v_i_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_a_929_; uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_lt(v_i_915_, v_sz_914_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_b_916_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v_snd_936_; lean_object* v_fst_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1048_; 
v___x_935_ = lean_st_ref_get(v___y_917_);
v_snd_936_ = lean_ctor_get(v_b_916_, 1);
v_fst_937_ = lean_ctor_get(v_b_916_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_b_916_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_939_ = v_b_916_;
v_isShared_940_ = v_isSharedCheck_1048_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_937_);
lean_dec(v_b_916_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1048_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1047_; 
v_fst_941_ = lean_ctor_get(v_snd_936_, 0);
v_snd_942_ = lean_ctor_get(v_snd_936_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_snd_936_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_944_ = v_snd_936_;
v_isShared_945_ = v_isSharedCheck_1047_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_941_);
lean_dec(v_snd_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1047_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_map_947_; lean_object* v_candidates_948_; lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_957_ = lean_array_uget_borrowed(v_as_913_, v_i_915_);
v___x_958_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_935_, v_a_957_);
lean_dec(v___x_935_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1044_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1044_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_val_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1044_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v_hasTheoryVar_1003_; lean_object* v___x_1004_; 
v_hasTheoryVar_1003_ = lean_ctor_get(v_ctx_911_, 1);
lean_inc_ref(v_hasTheoryVar_1003_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v_val_959_);
v___x_1004_ = lean_apply_12(v_hasTheoryVar_1003_, v_val_959_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; uint8_t v___x_1006_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = lean_unbox(v_a_1005_);
lean_dec(v_a_1005_);
if (v___x_1006_ == 0)
{
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
v_map_947_ = v_fst_937_;
v_candidates_948_ = v_fst_941_;
goto v___jp_946_;
}
else
{
lean_object* v_toCold_1007_; lean_object* v_options_1008_; uint8_t v_hasTrace_1009_; 
v_toCold_1007_ = lean_ctor_get(v___y_925_, 0);
v_options_1008_ = lean_ctor_get(v_toCold_1007_, 2);
v_hasTrace_1009_ = lean_ctor_get_uint8(v_options_1008_, sizeof(void*)*1);
if (v_hasTrace_1009_ == 0)
{
lean_del_object(v___x_961_);
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
goto v___jp_963_;
}
else
{
lean_object* v_inheritedTraceOptions_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_inheritedTraceOptions_1010_ = lean_ctor_get(v_toCold_1007_, 11);
v___x_1011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1010_, v_options_1008_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_del_object(v___x_961_);
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
goto v___jp_963_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_inc(v_val_959_);
v___x_1014_ = l_Lean_MessageData_ofExpr(v_val_959_);
v___x_1015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_inc_ref(v___x_912_);
v___x_1017_ = l_Lean_MessageData_ofExpr(v___x_912_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
lean_inc(v_snd_942_);
v___x_1021_ = l_Nat_reprFast(v_snd_942_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 0, v___x_1021_);
v___x_1023_ = v___x_961_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = l_Lean_MessageData_ofFormat(v___x_1023_);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1020_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1011_, v___x_1025_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref_known(v___x_1026_, 1);
v___y_964_ = v___y_917_;
v___y_965_ = v___y_918_;
v___y_966_ = v___y_919_;
v___y_967_ = v___y_920_;
v___y_968_ = v___y_921_;
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
goto v___jp_963_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_val_959_);
lean_del_object(v___x_944_);
lean_dec(v_snd_942_);
lean_dec(v_fst_941_);
lean_del_object(v___x_939_);
lean_dec(v_fst_937_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
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
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_del_object(v___x_944_);
lean_dec(v_snd_942_);
lean_dec(v_fst_941_);
lean_del_object(v___x_939_);
lean_dec(v_fst_937_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v_a_1036_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1004_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1004_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
v___jp_963_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref_n(v_e_910_, 2);
lean_inc(v_val_959_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_val_959_);
lean_ctor_set(v___x_974_, 1, v_e_910_);
v___x_975_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_910_, v_snd_942_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_937_, v_a_976_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; uint8_t v___x_979_; 
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_959_, v_val_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_inc(v_snd_942_);
lean_inc_ref(v___x_974_);
lean_inc_ref(v_ctx_911_);
v___x_980_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_911_, v_val_959_, v___x_974_, v_snd_942_, v_val_978_, v_fst_941_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_974_);
lean_ctor_set(v___x_982_, 1, v_val_978_);
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_937_, v_a_976_, v___x_982_);
v_map_947_ = v___x_983_;
v_candidates_948_ = v_a_981_;
goto v___jp_946_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_val_978_);
lean_dec(v_a_976_);
lean_dec_ref_known(v___x_974_, 2);
lean_del_object(v___x_944_);
lean_dec(v_snd_942_);
lean_del_object(v___x_939_);
lean_dec(v_fst_937_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v_a_984_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_980_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_dec(v_val_978_);
lean_dec(v_a_976_);
lean_dec_ref_known(v___x_974_, 2);
lean_dec(v_val_959_);
v_map_947_ = v_fst_937_;
v_candidates_948_ = v_fst_941_;
goto v___jp_946_;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v___x_977_);
lean_dec(v_val_959_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_974_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_937_, v_a_976_, v___x_993_);
v_map_947_ = v___x_994_;
v_candidates_948_ = v_fst_941_;
goto v___jp_946_;
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref_known(v___x_974_, 2);
lean_dec(v_val_959_);
lean_del_object(v___x_944_);
lean_dec(v_snd_942_);
lean_dec(v_fst_941_);
lean_del_object(v___x_939_);
lean_dec(v_fst_937_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v_a_995_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_975_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_975_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_958_);
lean_del_object(v___x_944_);
lean_del_object(v___x_939_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_fst_941_);
lean_ctor_set(v___x_1045_, 1, v_snd_942_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_fst_937_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v_a_929_ = v___x_1046_;
goto v___jp_928_;
}
v___jp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_snd_942_, v___x_949_);
lean_dec(v_snd_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_950_);
lean_ctor_set(v___x_944_, 0, v_candidates_948_);
v___x_952_ = v___x_944_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_candidates_948_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_952_);
lean_ctor_set(v___x_939_, 0, v_map_947_);
v___x_954_ = v___x_939_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_map_947_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_a_929_ = v___x_954_;
goto v___jp_928_;
}
}
}
}
}
}
v___jp_928_:
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_915_, v___x_930_);
v_i_915_ = v___x_931_;
v_b_916_ = v_a_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1049_ = _args[0];
lean_object* v_ctx_1050_ = _args[1];
lean_object* v___x_1051_ = _args[2];
lean_object* v_as_1052_ = _args[3];
lean_object* v_sz_1053_ = _args[4];
lean_object* v_i_1054_ = _args[5];
lean_object* v_b_1055_ = _args[6];
lean_object* v___y_1056_ = _args[7];
lean_object* v___y_1057_ = _args[8];
lean_object* v___y_1058_ = _args[9];
lean_object* v___y_1059_ = _args[10];
lean_object* v___y_1060_ = _args[11];
lean_object* v___y_1061_ = _args[12];
lean_object* v___y_1062_ = _args[13];
lean_object* v___y_1063_ = _args[14];
lean_object* v___y_1064_ = _args[15];
lean_object* v___y_1065_ = _args[16];
lean_object* v___y_1066_ = _args[17];
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1049_, v_ctx_1050_, v___x_1051_, v_as_1052_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1070_, uint8_t v_a_1071_, lean_object* v_as_1072_, size_t v_sz_1073_, size_t v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1074_, v_sz_1073_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec_ref(v_ctx_1070_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_b_1075_);
return v___x_1088_;
}
else
{
lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1191_; 
v_snd_1089_ = lean_ctor_get(v_b_1075_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_b_1075_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_b_1075_, 0);
lean_dec(v_unused_1192_);
v___x_1091_ = v_b_1075_;
v_isShared_1092_ = v_isSharedCheck_1191_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_dec(v_b_1075_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1191_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1190_; 
v_fst_1093_ = lean_ctor_get(v_snd_1089_, 0);
v_snd_1094_ = lean_ctor_get(v_snd_1089_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_snd_1089_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1096_ = v_snd_1089_;
v_isShared_1097_ = v_isSharedCheck_1190_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_snd_1089_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1190_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v_a_1100_; lean_object* v_a_1113_; uint8_t v___y_1187_; uint8_t v___x_1188_; 
v___x_1098_ = lean_box(0);
v_a_1113_ = lean_array_uget_borrowed(v_as_1072_, v_i_1074_);
v___x_1188_ = l_Lean_Expr_isApp(v_a_1113_);
if (v___x_1188_ == 0)
{
v___y_1187_ = v_a_1071_;
goto v___jp_1186_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = l_Lean_Expr_isEq(v_a_1113_);
if (v___x_1189_ == 0)
{
goto v___jp_1114_;
}
else
{
v___y_1187_ = v_a_1071_;
goto v___jp_1186_;
}
}
v___jp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_a_1100_);
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1102_ = v___x_1096_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_1100_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
size_t v___x_1103_; size_t v___x_1104_; 
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1074_, v___x_1103_);
v_i_1074_ = v___x_1104_;
v_b_1075_ = v___x_1102_;
goto _start;
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_snd_1094_);
lean_ctor_set(v___x_1091_, 0, v_fst_1093_);
v___x_1109_ = v___x_1091_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1093_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1094_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v_a_1100_ = v___x_1109_;
goto v___jp_1099_;
}
}
v___jp_1111_:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_fst_1093_);
lean_ctor_set(v___x_1112_, 1, v_snd_1094_);
v_a_1100_ = v___x_1112_;
goto v___jp_1099_;
}
v___jp_1114_:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_Expr_isHEq(v_a_1113_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_inc(v_a_1113_);
v___x_1116_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1113_, v___y_1076_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; uint8_t v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_del_object(v___x_1091_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_fst_1093_);
lean_ctor_set(v___x_1119_, 1, v_snd_1094_);
v_a_1100_ = v___x_1119_;
goto v___jp_1099_;
}
else
{
lean_object* v_isInterpreted_1120_; lean_object* v___x_1121_; 
v_isInterpreted_1120_ = lean_ctor_get(v_ctx_1070_, 0);
lean_inc_ref(v_isInterpreted_1120_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc(v_a_1113_);
v___x_1121_ = lean_apply_12(v_isInterpreted_1120_, v_a_1113_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; uint8_t v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_unbox(v_a_1122_);
lean_dec(v_a_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = l_Lean_Expr_getAppFn(v_a_1113_);
lean_inc_ref(v___x_1124_);
v___x_1125_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1124_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; uint8_t v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = lean_unbox(v_a_1126_);
lean_dec(v_a_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1124_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v_dummy_1130_; lean_object* v_nargs_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
lean_del_object(v___x_1091_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_dummy_1130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1131_ = l_Lean_Expr_getAppNumArgs(v_a_1113_);
lean_inc(v_nargs_1131_);
v___x_1132_ = lean_mk_array(v_nargs_1131_, v_dummy_1130_);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_sub(v_nargs_1131_, v___x_1133_);
lean_dec(v_nargs_1131_);
lean_inc_n(v_a_1113_, 2);
v___x_1135_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1113_, v___x_1132_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_snd_1094_);
lean_ctor_set(v___x_1136_, 1, v___x_1129_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_fst_1093_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v_sz_1138_ = lean_array_size(v___x_1135_);
v___x_1139_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1070_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1113_, v_ctx_1070_, v___x_1124_, v___x_1135_, v_sz_1138_, v___x_1139_, v___x_1137_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec_ref(v___x_1135_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_snd_1142_; lean_object* v_fst_1143_; lean_object* v_fst_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v_snd_1142_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_snd_1142_);
v_fst_1143_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_fst_1143_);
lean_dec(v_a_1141_);
v_fst_1144_ = lean_ctor_get(v_snd_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_snd_1142_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_snd_1142_, 1);
lean_dec(v_unused_1152_);
v___x_1146_ = v_snd_1142_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_fst_1144_);
lean_dec(v_snd_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v_fst_1144_);
lean_ctor_set(v___x_1146_, 0, v_fst_1143_);
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_fst_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_fst_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1100_ = v___x_1149_;
goto v___jp_1099_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1096_);
lean_dec_ref(v_ctx_1070_);
v_a_1153_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1140_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1140_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_dec_ref(v___x_1124_);
goto v___jp_1107_;
}
}
else
{
lean_dec_ref(v___x_1124_);
goto v___jp_1107_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___x_1124_);
lean_del_object(v___x_1096_);
lean_dec(v_snd_1094_);
lean_dec(v_fst_1093_);
lean_del_object(v___x_1091_);
lean_dec_ref(v_ctx_1070_);
v_a_1161_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1125_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1125_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v___x_1169_; 
lean_del_object(v___x_1091_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_fst_1093_);
lean_ctor_set(v___x_1169_, 1, v_snd_1094_);
v_a_1100_ = v___x_1169_;
goto v___jp_1099_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1096_);
lean_dec(v_snd_1094_);
lean_dec(v_fst_1093_);
lean_del_object(v___x_1091_);
lean_dec_ref(v_ctx_1070_);
v_a_1170_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1121_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1121_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1096_);
lean_dec(v_snd_1094_);
lean_dec(v_fst_1093_);
lean_del_object(v___x_1091_);
lean_dec_ref(v_ctx_1070_);
v_a_1178_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1116_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1116_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_del_object(v___x_1091_);
goto v___jp_1111_;
}
}
v___jp_1186_:
{
if (v___y_1187_ == 0)
{
lean_del_object(v___x_1091_);
goto v___jp_1111_;
}
else
{
goto v___jp_1114_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object** _args){
lean_object* v_ctx_1193_ = _args[0];
lean_object* v_a_1194_ = _args[1];
lean_object* v_as_1195_ = _args[2];
lean_object* v_sz_1196_ = _args[3];
lean_object* v_i_1197_ = _args[4];
lean_object* v_b_1198_ = _args[5];
lean_object* v___y_1199_ = _args[6];
lean_object* v___y_1200_ = _args[7];
lean_object* v___y_1201_ = _args[8];
lean_object* v___y_1202_ = _args[9];
lean_object* v___y_1203_ = _args[10];
lean_object* v___y_1204_ = _args[11];
lean_object* v___y_1205_ = _args[12];
lean_object* v___y_1206_ = _args[13];
lean_object* v___y_1207_ = _args[14];
lean_object* v___y_1208_ = _args[15];
lean_object* v___y_1209_ = _args[16];
_start:
{
uint8_t v_a_162234__boxed_1210_; size_t v_sz_boxed_1211_; size_t v_i_boxed_1212_; lean_object* v_res_1213_; 
v_a_162234__boxed_1210_ = lean_unbox(v_a_1194_);
v_sz_boxed_1211_ = lean_unbox_usize(v_sz_1196_);
lean_dec(v_sz_1196_);
v_i_boxed_1212_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1193_, v_a_162234__boxed_1210_, v_as_1195_, v_sz_boxed_1211_, v_i_boxed_1212_, v_b_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v_as_1195_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1214_, uint8_t v_a_1215_, lean_object* v_as_1216_, size_t v_sz_1217_, size_t v_i_1218_, lean_object* v_b_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_usize_dec_lt(v_i_1218_, v_sz_1217_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec_ref(v_ctx_1214_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_b_1219_);
return v___x_1232_;
}
else
{
lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1335_; 
v_snd_1233_ = lean_ctor_get(v_b_1219_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_b_1219_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_b_1219_, 0);
lean_dec(v_unused_1336_);
v___x_1235_ = v_b_1219_;
v_isShared_1236_ = v_isSharedCheck_1335_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_dec(v_b_1219_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1335_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1334_; 
v_fst_1237_ = lean_ctor_get(v_snd_1233_, 0);
v_snd_1238_ = lean_ctor_get(v_snd_1233_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_snd_1233_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1240_ = v_snd_1233_;
v_isShared_1241_ = v_isSharedCheck_1334_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_inc(v_fst_1237_);
lean_dec(v_snd_1233_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1334_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v_a_1244_; lean_object* v_a_1257_; uint8_t v___y_1331_; uint8_t v___x_1332_; 
v___x_1242_ = lean_box(0);
v_a_1257_ = lean_array_uget_borrowed(v_as_1216_, v_i_1218_);
v___x_1332_ = l_Lean_Expr_isApp(v_a_1257_);
if (v___x_1332_ == 0)
{
v___y_1331_ = v_a_1215_;
goto v___jp_1330_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_Expr_isEq(v_a_1257_);
if (v___x_1333_ == 0)
{
goto v___jp_1258_;
}
else
{
v___y_1331_ = v_a_1215_;
goto v___jp_1330_;
}
}
v___jp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v_a_1244_);
lean_ctor_set(v___x_1240_, 0, v___x_1242_);
v___x_1246_ = v___x_1240_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1244_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1218_, v___x_1247_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1214_, v_a_1215_, v_as_1216_, v_sz_1217_, v___x_1248_, v___x_1246_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1249_;
}
}
v___jp_1251_:
{
lean_object* v___x_1253_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_snd_1238_);
lean_ctor_set(v___x_1235_, 0, v_fst_1237_);
v___x_1253_ = v___x_1235_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_fst_1237_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_snd_1238_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v_a_1244_ = v___x_1253_;
goto v___jp_1243_;
}
}
v___jp_1255_:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_fst_1237_);
lean_ctor_set(v___x_1256_, 1, v_snd_1238_);
v_a_1244_ = v___x_1256_;
goto v___jp_1243_;
}
v___jp_1258_:
{
uint8_t v___x_1259_; 
v___x_1259_ = l_Lean_Expr_isHEq(v_a_1257_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_inc(v_a_1257_);
v___x_1260_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1257_, v___y_1220_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; uint8_t v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = lean_unbox(v_a_1261_);
lean_dec(v_a_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_del_object(v___x_1235_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_fst_1237_);
lean_ctor_set(v___x_1263_, 1, v_snd_1238_);
v_a_1244_ = v___x_1263_;
goto v___jp_1243_;
}
else
{
lean_object* v_isInterpreted_1264_; lean_object* v___x_1265_; 
v_isInterpreted_1264_ = lean_ctor_get(v_ctx_1214_, 0);
lean_inc_ref(v_isInterpreted_1264_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc(v_a_1257_);
v___x_1265_ = lean_apply_12(v_isInterpreted_1264_, v_a_1257_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, lean_box(0));
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; uint8_t v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = lean_unbox(v_a_1266_);
lean_dec(v_a_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = l_Lean_Expr_getAppFn(v_a_1257_);
lean_inc_ref(v___x_1268_);
v___x_1269_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1268_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1268_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v_dummy_1274_; lean_object* v_nargs_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; size_t v_sz_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
lean_del_object(v___x_1235_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v_dummy_1274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1275_ = l_Lean_Expr_getAppNumArgs(v_a_1257_);
lean_inc(v_nargs_1275_);
v___x_1276_ = lean_mk_array(v_nargs_1275_, v_dummy_1274_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_sub(v_nargs_1275_, v___x_1277_);
lean_dec(v_nargs_1275_);
lean_inc_n(v_a_1257_, 2);
v___x_1279_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1257_, v___x_1276_, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_snd_1238_);
lean_ctor_set(v___x_1280_, 1, v___x_1273_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_fst_1237_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v_sz_1282_ = lean_array_size(v___x_1279_);
v___x_1283_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1214_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1257_, v_ctx_1214_, v___x_1268_, v___x_1279_, v_sz_1282_, v___x_1283_, v___x_1281_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec_ref(v___x_1279_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_snd_1286_; lean_object* v_fst_1287_; lean_object* v_fst_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_snd_1286_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_snd_1286_);
v_fst_1287_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_fst_1287_);
lean_dec(v_a_1285_);
v_fst_1288_ = lean_ctor_get(v_snd_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_snd_1286_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_snd_1286_, 1);
lean_dec(v_unused_1296_);
v___x_1290_ = v_snd_1286_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_fst_1288_);
lean_dec(v_snd_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_fst_1288_);
lean_ctor_set(v___x_1290_, 0, v_fst_1287_);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_fst_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
v_a_1244_ = v___x_1293_;
goto v___jp_1243_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1240_);
lean_dec_ref(v_ctx_1214_);
v_a_1297_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1284_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1284_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_dec_ref(v___x_1268_);
goto v___jp_1251_;
}
}
else
{
lean_dec_ref(v___x_1268_);
goto v___jp_1251_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v___x_1268_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
lean_dec(v_fst_1237_);
lean_del_object(v___x_1235_);
lean_dec_ref(v_ctx_1214_);
v_a_1305_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1269_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1269_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v___x_1313_; 
lean_del_object(v___x_1235_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_fst_1237_);
lean_ctor_set(v___x_1313_, 1, v_snd_1238_);
v_a_1244_ = v___x_1313_;
goto v___jp_1243_;
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
lean_dec(v_fst_1237_);
lean_del_object(v___x_1235_);
lean_dec_ref(v_ctx_1214_);
v_a_1314_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1265_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1265_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
lean_dec(v_fst_1237_);
lean_del_object(v___x_1235_);
lean_dec_ref(v_ctx_1214_);
v_a_1322_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1260_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1260_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_del_object(v___x_1235_);
goto v___jp_1255_;
}
}
v___jp_1330_:
{
if (v___y_1331_ == 0)
{
lean_del_object(v___x_1235_);
goto v___jp_1255_;
}
else
{
goto v___jp_1258_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args){
lean_object* v_ctx_1337_ = _args[0];
lean_object* v_a_1338_ = _args[1];
lean_object* v_as_1339_ = _args[2];
lean_object* v_sz_1340_ = _args[3];
lean_object* v_i_1341_ = _args[4];
lean_object* v_b_1342_ = _args[5];
lean_object* v___y_1343_ = _args[6];
lean_object* v___y_1344_ = _args[7];
lean_object* v___y_1345_ = _args[8];
lean_object* v___y_1346_ = _args[9];
lean_object* v___y_1347_ = _args[10];
lean_object* v___y_1348_ = _args[11];
lean_object* v___y_1349_ = _args[12];
lean_object* v___y_1350_ = _args[13];
lean_object* v___y_1351_ = _args[14];
lean_object* v___y_1352_ = _args[15];
lean_object* v___y_1353_ = _args[16];
_start:
{
uint8_t v_a_162462__boxed_1354_; size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v_a_162462__boxed_1354_ = lean_unbox(v_a_1338_);
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1340_);
lean_dec(v_sz_1340_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1341_);
lean_dec(v_i_1341_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1337_, v_a_162462__boxed_1354_, v_as_1339_, v_sz_boxed_1355_, v_i_boxed_1356_, v_b_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v_as_1339_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1358_, uint8_t v_a_1359_, lean_object* v_as_1360_, size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_usize_dec_lt(v_i_1362_, v_sz_1361_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v_ctx_1358_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_b_1363_);
return v___x_1376_;
}
else
{
lean_object* v_snd_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1479_; 
v_snd_1377_ = lean_ctor_get(v_b_1363_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1480_);
v___x_1379_ = v_b_1363_;
v_isShared_1380_ = v_isSharedCheck_1479_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_snd_1377_);
lean_dec(v_b_1363_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1479_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1478_; 
v_fst_1381_ = lean_ctor_get(v_snd_1377_, 0);
v_snd_1382_ = lean_ctor_get(v_snd_1377_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_snd_1377_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1384_ = v_snd_1377_;
v_isShared_1385_ = v_isSharedCheck_1478_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_snd_1382_);
lean_inc(v_fst_1381_);
lean_dec(v_snd_1377_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1478_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v_a_1388_; lean_object* v_a_1401_; uint8_t v___y_1475_; uint8_t v___x_1476_; 
v___x_1386_ = lean_box(0);
v_a_1401_ = lean_array_uget_borrowed(v_as_1360_, v_i_1362_);
v___x_1476_ = l_Lean_Expr_isApp(v_a_1401_);
if (v___x_1476_ == 0)
{
v___y_1475_ = v_a_1359_;
goto v___jp_1474_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = l_Lean_Expr_isEq(v_a_1401_);
if (v___x_1477_ == 0)
{
goto v___jp_1402_;
}
else
{
v___y_1475_ = v_a_1359_;
goto v___jp_1474_;
}
}
v___jp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_a_1388_);
lean_ctor_set(v___x_1384_, 0, v___x_1386_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_a_1388_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
size_t v___x_1391_; size_t v___x_1392_; 
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_add(v_i_1362_, v___x_1391_);
v_i_1362_ = v___x_1392_;
v_b_1363_ = v___x_1390_;
goto _start;
}
}
v___jp_1395_:
{
lean_object* v___x_1397_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v_snd_1382_);
lean_ctor_set(v___x_1379_, 0, v_fst_1381_);
v___x_1397_ = v___x_1379_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_fst_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_snd_1382_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v_a_1388_ = v___x_1397_;
goto v___jp_1387_;
}
}
v___jp_1399_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_fst_1381_);
lean_ctor_set(v___x_1400_, 1, v_snd_1382_);
v_a_1388_ = v___x_1400_;
goto v___jp_1387_;
}
v___jp_1402_:
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Expr_isHEq(v_a_1401_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_inc(v_a_1401_);
v___x_1404_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1401_, v___y_1364_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; uint8_t v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = lean_unbox(v_a_1405_);
lean_dec(v_a_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_del_object(v___x_1379_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_fst_1381_);
lean_ctor_set(v___x_1407_, 1, v_snd_1382_);
v_a_1388_ = v___x_1407_;
goto v___jp_1387_;
}
else
{
lean_object* v_isInterpreted_1408_; lean_object* v___x_1409_; 
v_isInterpreted_1408_ = lean_ctor_get(v_ctx_1358_, 0);
lean_inc_ref(v_isInterpreted_1408_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc_ref(v___y_1366_);
lean_inc(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc(v_a_1401_);
v___x_1409_ = lean_apply_12(v_isInterpreted_1408_, v_a_1401_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, lean_box(0));
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; uint8_t v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = lean_unbox(v_a_1410_);
lean_dec(v_a_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = l_Lean_Expr_getAppFn(v_a_1401_);
lean_inc_ref(v___x_1412_);
v___x_1413_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1412_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; uint8_t v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = lean_unbox(v_a_1414_);
lean_dec(v_a_1414_);
if (v___x_1415_ == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1412_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v_dummy_1418_; lean_object* v_nargs_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; size_t v_sz_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1379_);
v___x_1417_ = lean_unsigned_to_nat(0u);
v_dummy_1418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1419_ = l_Lean_Expr_getAppNumArgs(v_a_1401_);
lean_inc(v_nargs_1419_);
v___x_1420_ = lean_mk_array(v_nargs_1419_, v_dummy_1418_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_sub(v_nargs_1419_, v___x_1421_);
lean_dec(v_nargs_1419_);
lean_inc_n(v_a_1401_, 2);
v___x_1423_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1401_, v___x_1420_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_snd_1382_);
lean_ctor_set(v___x_1424_, 1, v___x_1417_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_fst_1381_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v_sz_1426_ = lean_array_size(v___x_1423_);
v___x_1427_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1358_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1401_, v_ctx_1358_, v___x_1412_, v___x_1423_, v_sz_1426_, v___x_1427_, v___x_1425_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec_ref(v___x_1423_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v_snd_1430_; lean_object* v_fst_1431_; lean_object* v_fst_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v_snd_1430_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_snd_1430_);
v_fst_1431_ = lean_ctor_get(v_a_1429_, 0);
lean_inc(v_fst_1431_);
lean_dec(v_a_1429_);
v_fst_1432_ = lean_ctor_get(v_snd_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_snd_1430_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_snd_1430_, 1);
lean_dec(v_unused_1440_);
v___x_1434_ = v_snd_1430_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_fst_1432_);
lean_dec(v_snd_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_fst_1432_);
lean_ctor_set(v___x_1434_, 0, v_fst_1431_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_fst_1431_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_fst_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v_a_1388_ = v___x_1437_;
goto v___jp_1387_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_del_object(v___x_1384_);
lean_dec_ref(v_ctx_1358_);
v_a_1441_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1428_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1428_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_dec_ref(v___x_1412_);
goto v___jp_1395_;
}
}
else
{
lean_dec_ref(v___x_1412_);
goto v___jp_1395_;
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1384_);
lean_dec(v_snd_1382_);
lean_dec(v_fst_1381_);
lean_del_object(v___x_1379_);
lean_dec_ref(v_ctx_1358_);
v_a_1449_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1413_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1413_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v___x_1457_; 
lean_del_object(v___x_1379_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_fst_1381_);
lean_ctor_set(v___x_1457_, 1, v_snd_1382_);
v_a_1388_ = v___x_1457_;
goto v___jp_1387_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_del_object(v___x_1384_);
lean_dec(v_snd_1382_);
lean_dec(v_fst_1381_);
lean_del_object(v___x_1379_);
lean_dec_ref(v_ctx_1358_);
v_a_1458_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1409_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1409_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1384_);
lean_dec(v_snd_1382_);
lean_dec(v_fst_1381_);
lean_del_object(v___x_1379_);
lean_dec_ref(v_ctx_1358_);
v_a_1466_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1404_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1404_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_del_object(v___x_1379_);
goto v___jp_1399_;
}
}
v___jp_1474_:
{
if (v___y_1475_ == 0)
{
lean_del_object(v___x_1379_);
goto v___jp_1399_;
}
else
{
goto v___jp_1402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object** _args){
lean_object* v_ctx_1481_ = _args[0];
lean_object* v_a_1482_ = _args[1];
lean_object* v_as_1483_ = _args[2];
lean_object* v_sz_1484_ = _args[3];
lean_object* v_i_1485_ = _args[4];
lean_object* v_b_1486_ = _args[5];
lean_object* v___y_1487_ = _args[6];
lean_object* v___y_1488_ = _args[7];
lean_object* v___y_1489_ = _args[8];
lean_object* v___y_1490_ = _args[9];
lean_object* v___y_1491_ = _args[10];
lean_object* v___y_1492_ = _args[11];
lean_object* v___y_1493_ = _args[12];
lean_object* v___y_1494_ = _args[13];
lean_object* v___y_1495_ = _args[14];
lean_object* v___y_1496_ = _args[15];
lean_object* v___y_1497_ = _args[16];
_start:
{
uint8_t v_a_162690__boxed_1498_; size_t v_sz_boxed_1499_; size_t v_i_boxed_1500_; lean_object* v_res_1501_; 
v_a_162690__boxed_1498_ = lean_unbox(v_a_1482_);
v_sz_boxed_1499_ = lean_unbox_usize(v_sz_1484_);
lean_dec(v_sz_1484_);
v_i_boxed_1500_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1481_, v_a_162690__boxed_1498_, v_as_1483_, v_sz_boxed_1499_, v_i_boxed_1500_, v_b_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v_as_1483_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1502_, uint8_t v_a_1503_, lean_object* v_as_1504_, size_t v_sz_1505_, size_t v_i_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1506_, v_sz_1505_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_dec_ref(v_ctx_1502_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_b_1507_);
return v___x_1520_;
}
else
{
lean_object* v_snd_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1623_; 
v_snd_1521_ = lean_ctor_get(v_b_1507_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_b_1507_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_b_1507_, 0);
lean_dec(v_unused_1624_);
v___x_1523_ = v_b_1507_;
v_isShared_1524_ = v_isSharedCheck_1623_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1521_);
lean_dec(v_b_1507_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1623_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1622_; 
v_fst_1525_ = lean_ctor_get(v_snd_1521_, 0);
v_snd_1526_ = lean_ctor_get(v_snd_1521_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_snd_1521_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1528_ = v_snd_1521_;
v_isShared_1529_ = v_isSharedCheck_1622_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_inc(v_fst_1525_);
lean_dec(v_snd_1521_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1622_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v_a_1532_; lean_object* v_a_1545_; uint8_t v___y_1619_; uint8_t v___x_1620_; 
v___x_1530_ = lean_box(0);
v_a_1545_ = lean_array_uget_borrowed(v_as_1504_, v_i_1506_);
v___x_1620_ = l_Lean_Expr_isApp(v_a_1545_);
if (v___x_1620_ == 0)
{
v___y_1619_ = v_a_1503_;
goto v___jp_1618_;
}
else
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Expr_isEq(v_a_1545_);
if (v___x_1621_ == 0)
{
goto v___jp_1546_;
}
else
{
v___y_1619_ = v_a_1503_;
goto v___jp_1618_;
}
}
v___jp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1532_);
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_a_1532_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1506_, v___x_1535_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1502_, v_a_1503_, v_as_1504_, v_sz_1505_, v___x_1536_, v___x_1534_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1537_;
}
}
v___jp_1539_:
{
lean_object* v___x_1541_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v_snd_1526_);
lean_ctor_set(v___x_1523_, 0, v_fst_1525_);
v___x_1541_ = v___x_1523_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_fst_1525_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_snd_1526_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
v_a_1532_ = v___x_1541_;
goto v___jp_1531_;
}
}
v___jp_1543_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_fst_1525_);
lean_ctor_set(v___x_1544_, 1, v_snd_1526_);
v_a_1532_ = v___x_1544_;
goto v___jp_1531_;
}
v___jp_1546_:
{
uint8_t v___x_1547_; 
v___x_1547_ = l_Lean_Expr_isHEq(v_a_1545_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_inc(v_a_1545_);
v___x_1548_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1545_, v___y_1508_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; uint8_t v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_unbox(v_a_1549_);
lean_dec(v_a_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_del_object(v___x_1523_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_fst_1525_);
lean_ctor_set(v___x_1551_, 1, v_snd_1526_);
v_a_1532_ = v___x_1551_;
goto v___jp_1531_;
}
else
{
lean_object* v_isInterpreted_1552_; lean_object* v___x_1553_; 
v_isInterpreted_1552_ = lean_ctor_get(v_ctx_1502_, 0);
lean_inc_ref(v_isInterpreted_1552_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1510_);
lean_inc(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc(v_a_1545_);
v___x_1553_ = lean_apply_12(v_isInterpreted_1552_, v_a_1545_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; uint8_t v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = lean_unbox(v_a_1554_);
lean_dec(v_a_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_Expr_getAppFn(v_a_1545_);
lean_inc_ref(v___x_1556_);
v___x_1557_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1556_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = lean_unbox(v_a_1558_);
lean_dec(v_a_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1556_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v_dummy_1562_; lean_object* v_nargs_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; size_t v_sz_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1523_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v_dummy_1562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1563_ = l_Lean_Expr_getAppNumArgs(v_a_1545_);
lean_inc(v_nargs_1563_);
v___x_1564_ = lean_mk_array(v_nargs_1563_, v_dummy_1562_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_sub(v_nargs_1563_, v___x_1565_);
lean_dec(v_nargs_1563_);
lean_inc_n(v_a_1545_, 2);
v___x_1567_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1545_, v___x_1564_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_snd_1526_);
lean_ctor_set(v___x_1568_, 1, v___x_1561_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_fst_1525_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v_sz_1570_ = lean_array_size(v___x_1567_);
v___x_1571_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1502_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1545_, v_ctx_1502_, v___x_1556_, v___x_1567_, v_sz_1570_, v___x_1571_, v___x_1569_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec_ref(v___x_1567_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_snd_1574_; lean_object* v_fst_1575_; lean_object* v_fst_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_snd_1574_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_snd_1574_);
v_fst_1575_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_fst_1575_);
lean_dec(v_a_1573_);
v_fst_1576_ = lean_ctor_get(v_snd_1574_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_snd_1574_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_snd_1574_, 1);
lean_dec(v_unused_1584_);
v___x_1578_ = v_snd_1574_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_fst_1576_);
lean_dec(v_snd_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v_fst_1576_);
lean_ctor_set(v___x_1578_, 0, v_fst_1575_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_fst_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_fst_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v_a_1532_ = v___x_1581_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_del_object(v___x_1528_);
lean_dec_ref(v_ctx_1502_);
v_a_1585_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1572_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1572_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_dec_ref(v___x_1556_);
goto v___jp_1539_;
}
}
else
{
lean_dec_ref(v___x_1556_);
goto v___jp_1539_;
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v___x_1556_);
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
lean_dec_ref(v_ctx_1502_);
v_a_1593_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1557_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1557_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v___x_1601_; 
lean_del_object(v___x_1523_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_fst_1525_);
lean_ctor_set(v___x_1601_, 1, v_snd_1526_);
v_a_1532_ = v___x_1601_;
goto v___jp_1531_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
lean_dec_ref(v_ctx_1502_);
v_a_1602_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1553_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1553_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
lean_dec_ref(v_ctx_1502_);
v_a_1610_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1548_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1548_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_del_object(v___x_1523_);
goto v___jp_1543_;
}
}
v___jp_1618_:
{
if (v___y_1619_ == 0)
{
lean_del_object(v___x_1523_);
goto v___jp_1543_;
}
else
{
goto v___jp_1546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object** _args){
lean_object* v_ctx_1625_ = _args[0];
lean_object* v_a_1626_ = _args[1];
lean_object* v_as_1627_ = _args[2];
lean_object* v_sz_1628_ = _args[3];
lean_object* v_i_1629_ = _args[4];
lean_object* v_b_1630_ = _args[5];
lean_object* v___y_1631_ = _args[6];
lean_object* v___y_1632_ = _args[7];
lean_object* v___y_1633_ = _args[8];
lean_object* v___y_1634_ = _args[9];
lean_object* v___y_1635_ = _args[10];
lean_object* v___y_1636_ = _args[11];
lean_object* v___y_1637_ = _args[12];
lean_object* v___y_1638_ = _args[13];
lean_object* v___y_1639_ = _args[14];
lean_object* v___y_1640_ = _args[15];
lean_object* v___y_1641_ = _args[16];
_start:
{
uint8_t v_a_162918__boxed_1642_; size_t v_sz_boxed_1643_; size_t v_i_boxed_1644_; lean_object* v_res_1645_; 
v_a_162918__boxed_1642_ = lean_unbox(v_a_1626_);
v_sz_boxed_1643_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1644_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1625_, v_a_162918__boxed_1642_, v_as_1627_, v_sz_boxed_1643_, v_i_boxed_1644_, v_b_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v_as_1627_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1646_, lean_object* v_ctx_1647_, uint8_t v_a_1648_, lean_object* v_n_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
if (lean_obj_tag(v_n_1649_) == 0)
{
lean_object* v_cs_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
v_cs_1662_ = lean_ctor_get(v_n_1649_, 0);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_b_1650_);
v_sz_1665_ = lean_array_size(v_cs_1662_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1646_, v_ctx_1647_, v_a_1648_, v_cs_1662_, v_sz_1665_, v___x_1666_, v___x_1664_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1682_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_fst_1672_; 
v_fst_1672_ = lean_ctor_get(v_a_1668_, 0);
if (lean_obj_tag(v_fst_1672_) == 0)
{
lean_object* v_snd_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v_snd_1673_ = lean_ctor_get(v_a_1668_, 1);
lean_inc(v_snd_1673_);
lean_dec(v_a_1668_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_snd_1673_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1674_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1680_; 
lean_inc_ref(v_fst_1672_);
lean_dec(v_a_1668_);
v_val_1678_ = lean_ctor_get(v_fst_1672_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v_fst_1672_, 1);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_val_1678_);
v___x_1680_ = v___x_1670_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_val_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1667_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1667_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_vs_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v_vs_1691_ = lean_ctor_get(v_n_1649_, 0);
v___x_1692_ = lean_box(0);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_b_1650_);
v_sz_1694_ = lean_array_size(v_vs_1691_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1647_, v_a_1648_, v_vs_1691_, v_sz_1694_, v___x_1695_, v___x_1693_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1711_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1711_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1711_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_fst_1701_; 
v_fst_1701_ = lean_ctor_get(v_a_1697_, 0);
if (lean_obj_tag(v_fst_1701_) == 0)
{
lean_object* v_snd_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v_snd_1702_ = lean_ctor_get(v_a_1697_, 1);
lean_inc(v_snd_1702_);
lean_dec(v_a_1697_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_snd_1702_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1703_);
v___x_1705_ = v___x_1699_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
else
{
lean_object* v_val_1707_; lean_object* v___x_1709_; 
lean_inc_ref(v_fst_1701_);
lean_dec(v_a_1697_);
v_val_1707_ = lean_ctor_get(v_fst_1701_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v_fst_1701_, 1);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_val_1707_);
v___x_1709_ = v___x_1699_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_val_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1696_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1696_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1720_, lean_object* v_ctx_1721_, uint8_t v_a_1722_, lean_object* v_as_1723_, size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v_ctx_1721_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1726_);
return v___x_1739_;
}
else
{
lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1774_; 
v_snd_1740_ = lean_ctor_get(v_b_1726_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_b_1726_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_b_1726_, 0);
lean_dec(v_unused_1775_);
v___x_1742_ = v_b_1726_;
v_isShared_1743_ = v_isSharedCheck_1774_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_dec(v_b_1726_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1774_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_array_uget_borrowed(v_as_1723_, v_i_1725_);
lean_inc(v_snd_1740_);
lean_inc_ref(v_ctx_1721_);
v___x_1745_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1720_, v_ctx_1721_, v_a_1722_, v_a_1744_, v_snd_1740_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1765_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
if (lean_obj_tag(v_a_1746_) == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec_ref(v_ctx_1721_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_a_1746_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1750_);
v___x_1752_ = v___x_1742_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_snd_1740_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1752_);
v___x_1754_ = v___x_1748_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_del_object(v___x_1748_);
lean_dec(v_snd_1740_);
v_a_1757_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v_a_1746_, 1);
v___x_1758_ = lean_box(0);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1757_);
lean_ctor_set(v___x_1742_, 0, v___x_1758_);
v___x_1760_ = v___x_1742_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_a_1757_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1725_, v___x_1761_);
v_i_1725_ = v___x_1762_;
v_b_1726_ = v___x_1760_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_del_object(v___x_1742_);
lean_dec(v_snd_1740_);
lean_dec_ref(v_ctx_1721_);
v_a_1766_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1745_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1745_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1776_ = _args[0];
lean_object* v_ctx_1777_ = _args[1];
lean_object* v_a_1778_ = _args[2];
lean_object* v_as_1779_ = _args[3];
lean_object* v_sz_1780_ = _args[4];
lean_object* v_i_1781_ = _args[5];
lean_object* v_b_1782_ = _args[6];
lean_object* v___y_1783_ = _args[7];
lean_object* v___y_1784_ = _args[8];
lean_object* v___y_1785_ = _args[9];
lean_object* v___y_1786_ = _args[10];
lean_object* v___y_1787_ = _args[11];
lean_object* v___y_1788_ = _args[12];
lean_object* v___y_1789_ = _args[13];
lean_object* v___y_1790_ = _args[14];
lean_object* v___y_1791_ = _args[15];
lean_object* v___y_1792_ = _args[16];
lean_object* v___y_1793_ = _args[17];
_start:
{
uint8_t v_a_163145__boxed_1794_; size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; lean_object* v_res_1797_; 
v_a_163145__boxed_1794_ = lean_unbox(v_a_1778_);
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1776_, v_ctx_1777_, v_a_163145__boxed_1794_, v_as_1779_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v_as_1779_);
lean_dec_ref(v_init_1776_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1798_, lean_object* v_ctx_1799_, lean_object* v_a_1800_, lean_object* v_n_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_a_163173__boxed_1814_; lean_object* v_res_1815_; 
v_a_163173__boxed_1814_ = lean_unbox(v_a_1800_);
v_res_1815_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1798_, v_ctx_1799_, v_a_163173__boxed_1814_, v_n_1801_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v_n_1801_);
lean_dec_ref(v_init_1798_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1816_, uint8_t v_a_1817_, lean_object* v_t_1818_, lean_object* v_init_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_root_1831_; lean_object* v_tail_1832_; lean_object* v___x_1833_; 
v_root_1831_ = lean_ctor_get(v_t_1818_, 0);
v_tail_1832_ = lean_ctor_get(v_t_1818_, 1);
lean_inc_ref(v_ctx_1816_);
lean_inc_ref(v_init_1819_);
v___x_1833_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1819_, v_ctx_1816_, v_a_1817_, v_root_1831_, v_init_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec_ref(v_init_1819_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1870_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1870_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1870_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; 
lean_dec_ref(v_ctx_1816_);
v_a_1838_ = lean_ctor_get(v_a_1834_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v_a_1834_, 1);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_a_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; size_t v_sz_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1836_);
v_a_1842_ = lean_ctor_get(v_a_1834_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v_a_1834_, 1);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_a_1842_);
v_sz_1845_ = lean_array_size(v_tail_1832_);
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1816_, v_a_1817_, v_tail_1832_, v_sz_1845_, v___x_1846_, v___x_1844_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1861_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_fst_1852_; 
v_fst_1852_ = lean_ctor_get(v_a_1848_, 0);
if (lean_obj_tag(v_fst_1852_) == 0)
{
lean_object* v_snd_1853_; lean_object* v___x_1855_; 
v_snd_1853_ = lean_ctor_get(v_a_1848_, 1);
lean_inc(v_snd_1853_);
lean_dec(v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_snd_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_snd_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_object* v_val_1857_; lean_object* v___x_1859_; 
lean_inc_ref(v_fst_1852_);
lean_dec(v_a_1848_);
v_val_1857_ = lean_ctor_get(v_fst_1852_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v_fst_1852_, 1);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_val_1857_);
v___x_1859_ = v___x_1850_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_val_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1847_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1847_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_ctx_1816_);
v_a_1871_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1833_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1833_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1879_, lean_object* v_a_1880_, lean_object* v_t_1881_, lean_object* v_init_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_a_163394__boxed_1894_; lean_object* v_res_1895_; 
v_a_163394__boxed_1894_ = lean_unbox(v_a_1880_);
v_res_1895_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1879_, v_a_163394__boxed_1894_, v_t_1881_, v_init_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v_t_1881_);
return v_res_1895_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1901_ = l_Lean_Name_append(v___x_1900_, v___x_1899_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_a_1918_; uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
v___x_1924_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1923_, v___y_1906_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; uint8_t v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
if (lean_obj_tag(v___x_1923_) == 2)
{
lean_object* v_a_1927_; lean_object* v_b_1928_; lean_object* v_eq_1929_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v_toCold_1985_; lean_object* v_options_1986_; uint8_t v_hasTrace_1987_; 
v_a_1927_ = lean_ctor_get(v___x_1923_, 0);
v_b_1928_ = lean_ctor_get(v___x_1923_, 1);
v_eq_1929_ = lean_ctor_get(v___x_1923_, 3);
v_toCold_1985_ = lean_ctor_get(v___y_1914_, 0);
v_options_1986_ = lean_ctor_get(v_toCold_1985_, 2);
v_hasTrace_1987_ = lean_ctor_get_uint8(v_options_1986_, sizeof(void*)*1);
if (v_hasTrace_1987_ == 0)
{
v___y_1954_ = v___y_1906_;
v___y_1955_ = v___y_1907_;
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
goto v___jp_1953_;
}
else
{
lean_object* v_inheritedTraceOptions_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_toCold_1985_, 11);
v___x_1989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1986_, v___x_1990_);
if (v___x_1991_ == 0)
{
v___y_1954_ = v___y_1906_;
v___y_1955_ = v___y_1907_;
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_inc_ref(v_eq_1929_);
v___x_1992_ = l_Lean_MessageData_ofExpr(v_eq_1929_);
v___x_1993_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1989_, v___x_1992_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_dec_ref_known(v___x_1993_, 1);
v___y_1954_ = v___y_1906_;
v___y_1955_ = v___y_1907_;
v___y_1956_ = v___y_1908_;
v___y_1957_ = v___y_1909_;
v___y_1958_ = v___y_1910_;
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
goto v___jp_1953_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_b_1905_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
v___jp_1930_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_box(0);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1931_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1935_);
lean_inc(v___y_1940_);
lean_inc_ref(v_eq_1929_);
v___x_1943_ = lean_grind_internalize(v_eq_1929_, v___y_1941_, v___x_1942_, v___y_1940_, v___y_1935_, v___y_1938_, v___y_1934_, v___y_1937_, v___y_1939_, v___y_1931_, v___y_1936_, v___y_1933_, v___y_1932_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref_known(v___x_1943_, 1);
lean_inc_ref(v___x_1923_);
v___x_1944_ = lean_array_push(v_b_1905_, v___x_1923_);
v_a_1918_ = v___x_1944_;
goto v___jp_1917_;
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_b_1905_);
v_a_1945_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1943_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1927_, v___y_1954_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1928_, v___y_1954_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; uint8_t v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = lean_nat_dec_le(v_a_1965_, v_a_1967_);
if (v___x_1968_ == 0)
{
lean_dec(v_a_1967_);
v___y_1931_ = v___y_1960_;
v___y_1932_ = v___y_1963_;
v___y_1933_ = v___y_1962_;
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1955_;
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1958_;
v___y_1938_ = v___y_1956_;
v___y_1939_ = v___y_1959_;
v___y_1940_ = v___y_1954_;
v___y_1941_ = v_a_1965_;
goto v___jp_1930_;
}
else
{
lean_dec(v_a_1965_);
v___y_1931_ = v___y_1960_;
v___y_1932_ = v___y_1963_;
v___y_1933_ = v___y_1962_;
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1955_;
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1958_;
v___y_1938_ = v___y_1956_;
v___y_1939_ = v___y_1959_;
v___y_1940_ = v___y_1954_;
v___y_1941_ = v_a_1967_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_a_1965_);
lean_dec_ref(v_b_1905_);
v_a_1969_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1966_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1966_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_b_1905_);
v_a_1977_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1964_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1964_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
else
{
v_a_1918_ = v_b_1905_;
goto v___jp_1917_;
}
}
else
{
v_a_1918_ = v_b_1905_;
goto v___jp_1917_;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_b_1905_);
v_a_2002_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1924_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1924_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_b_1905_);
return v___x_2010_;
}
v___jp_1917_:
{
size_t v___x_1919_; size_t v___x_1920_; 
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1903_, v___x_1919_);
v_i_1903_ = v___x_1920_;
v_b_1905_ = v_a_1918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_stop_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
size_t v_i_boxed_2026_; size_t v_stop_boxed_2027_; lean_object* v_res_2028_; 
v_i_boxed_2026_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_stop_boxed_2027_ = lean_unbox_usize(v_stop_2013_);
lean_dec(v_stop_2013_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2011_, v_i_boxed_2026_, v_stop_boxed_2027_, v_b_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v_as_2011_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2031_, lean_object* v_start_2032_, lean_object* v_stop_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2046_ = lean_nat_dec_lt(v_start_2032_, v_stop_2033_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = lean_array_get_size(v_as_2031_);
v___x_2049_ = lean_nat_dec_le(v_stop_2033_, v___x_2048_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_nat_dec_lt(v_start_2032_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2045_);
return v___x_2051_;
}
else
{
size_t v___x_2052_; size_t v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_usize_of_nat(v_start_2032_);
v___x_2053_ = lean_usize_of_nat(v___x_2048_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2031_, v___x_2052_, v___x_2053_, v___x_2045_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
return v___x_2054_;
}
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = lean_usize_of_nat(v_start_2032_);
v___x_2056_ = lean_usize_of_nat(v_stop_2033_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2031_, v___x_2055_, v___x_2056_, v___x_2045_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2058_, lean_object* v_start_2059_, lean_object* v_stop_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2058_, v_start_2059_, v_stop_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec(v_stop_2060_);
lean_dec(v_start_2059_);
lean_dec_ref(v_as_2058_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_unsigned_to_nat(16u);
v___x_2075_ = lean_mk_array(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2090_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2301_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2301_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2301_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v_mbtc_2104_; 
v_mbtc_2104_ = lean_ctor_get_uint8(v_a_2100_, sizeof(void*)*14 + 18);
lean_dec(v_a_2100_);
if (v_mbtc_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec_ref(v_ctx_2087_);
v___x_2105_ = lean_box(v_mbtc_2104_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v___x_2109_; 
lean_del_object(v___x_2102_);
v___x_2109_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2088_, v_a_2090_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2300_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2300_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2300_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_unbox(v_a_2110_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v_toGoalState_2116_; lean_object* v_exprs_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
lean_del_object(v___x_2112_);
v___x_2115_ = lean_st_ref_get(v_a_2088_);
v_toGoalState_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_ref(v_toGoalState_2116_);
lean_dec(v___x_2115_);
v_exprs_2117_ = lean_ctor_get(v_toGoalState_2116_, 2);
lean_inc_ref(v_exprs_2117_);
lean_dec_ref(v_toGoalState_2116_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2120_ = lean_unbox(v_a_2110_);
v___x_2121_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2087_, v___x_2120_, v_exprs_2117_, v___x_2119_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec_ref(v_exprs_2117_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2286_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2286_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2286_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_snd_2126_; lean_object* v_size_2127_; lean_object* v_buckets_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2285_; 
v_snd_2126_ = lean_ctor_get(v_a_2122_, 1);
lean_inc(v_snd_2126_);
lean_dec(v_a_2122_);
v_size_2127_ = lean_ctor_get(v_snd_2126_, 0);
v_buckets_2128_ = lean_ctor_get(v_snd_2126_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_snd_2126_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2130_ = v_snd_2126_;
v_isShared_2131_ = v_isSharedCheck_2285_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_buckets_2128_);
lean_inc(v_size_2127_);
lean_dec(v_snd_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2285_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_eq(v_size_2127_, v___x_2118_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_del_object(v___x_2124_);
lean_dec(v_a_2110_);
v___x_2133_ = lean_st_ref_get(v_a_2088_);
v___x_2134_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2090_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_toGoalState_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2272_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_toGoalState_2136_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; 
v_unused_2273_ = lean_ctor_get(v___x_2133_, 1);
lean_dec(v_unused_2273_);
v___x_2138_ = v___x_2133_;
v_isShared_2139_ = v_isSharedCheck_2272_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_toGoalState_2136_);
lean_dec(v___x_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2272_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_split_2140_; lean_object* v_splits_2141_; lean_object* v_num_2142_; uint8_t v___x_2143_; lean_object* v___y_2145_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2201_; 
v_split_2140_ = lean_ctor_get(v_toGoalState_2136_, 14);
lean_inc_ref(v_split_2140_);
lean_dec_ref(v_toGoalState_2136_);
v_splits_2141_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_splits_2141_);
lean_dec(v_a_2135_);
v_num_2142_ = lean_ctor_get(v_split_2140_, 0);
lean_inc(v_num_2142_);
lean_dec_ref(v_split_2140_);
v___x_2143_ = lean_nat_dec_lt(v_splits_2141_, v_num_2142_);
lean_dec(v_num_2142_);
lean_dec(v_splits_2141_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
lean_del_object(v___x_2138_);
lean_del_object(v___x_2130_);
v___x_2207_ = lean_mk_empty_array_with_capacity(v_size_2127_);
lean_dec(v_size_2127_);
v___x_2208_ = lean_array_get_size(v_buckets_2128_);
v___x_2209_ = lean_nat_dec_lt(v___x_2118_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_dec_ref(v_buckets_2128_);
v___y_2201_ = v___x_2207_;
goto v___jp_2200_;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = lean_usize_of_nat(v___x_2208_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2128_, v___x_2210_, v___x_2211_, v___x_2207_);
lean_dec_ref(v_buckets_2128_);
v___y_2201_ = v___x_2212_;
goto v___jp_2200_;
}
}
else
{
lean_object* v___x_2213_; 
lean_dec_ref(v_buckets_2128_);
lean_dec(v_size_2127_);
v___x_2213_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2090_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2092_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2255_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2255_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2255_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
uint8_t v_verbose_2220_; 
v_verbose_2220_ = lean_ctor_get_uint8(v_a_2216_, 0);
lean_dec(v_a_2216_);
if (v_verbose_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_dec(v_a_2214_);
lean_del_object(v___x_2138_);
lean_del_object(v___x_2130_);
v___x_2221_ = lean_box(v___x_2132_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2221_);
v___x_2223_ = v___x_2218_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
lean_object* v_splits_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_del_object(v___x_2218_);
v_splits_2225_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_splits_2225_);
lean_dec(v_a_2214_);
v___x_2226_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2227_ = l_Nat_reprFast(v_splits_2225_);
v___x_2228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
v___x_2229_ = l_Lean_MessageData_ofFormat(v___x_2228_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set_tag(v___x_2138_, 7);
lean_ctor_set(v___x_2138_, 1, v___x_2229_);
lean_ctor_set(v___x_2138_, 0, v___x_2226_);
v___x_2231_ = v___x_2138_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 7);
lean_ctor_set(v___x_2130_, 1, v___x_2232_);
lean_ctor_set(v___x_2130_, 0, v___x_2231_);
v___x_2234_ = v___x_2130_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Meta_Sym_reportIssue(v___x_2234_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2235_, 0);
lean_dec(v_unused_2244_);
v___x_2237_ = v___x_2235_;
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v___x_2235_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(v___x_2132_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_a_2245_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2235_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2235_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
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
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2214_);
lean_del_object(v___x_2138_);
lean_del_object(v___x_2130_);
v_a_2256_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2215_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2215_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_del_object(v___x_2138_);
lean_del_object(v___x_2130_);
v_a_2264_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2213_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2213_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_array_get_size(v___y_2145_);
v___x_2147_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2145_, v___x_2118_, v___x_2146_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec_ref(v___y_2145_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2179_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2179_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2179_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_array_get_size(v_a_2148_);
v___x_2153_ = lean_nat_dec_eq(v___x_2152_, v___x_2118_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; size_t v_sz_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
lean_del_object(v___x_2150_);
v___x_2154_ = lean_box(0);
v_sz_2155_ = lean_array_size(v_a_2148_);
v___x_2156_ = ((size_t)0ULL);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2148_, v_sz_2155_, v___x_2156_, v___x_2154_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2148_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2157_, 0);
lean_dec(v_unused_2166_);
v___x_2159_ = v___x_2157_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_dec(v___x_2157_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(v_mbtc_2104_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2157_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2157_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_a_2148_);
v___x_2175_ = lean_box(v___x_2143_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2175_);
v___x_2177_ = v___x_2150_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2147_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2147_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
v___jp_2188_:
{
lean_object* v___x_2193_; 
v___x_2193_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2189_, v___y_2191_, v___y_2190_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec(v___y_2189_);
v___y_2145_ = v___x_2193_;
goto v___jp_2144_;
}
v___jp_2194_:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_nat_dec_le(v___y_2198_, v___y_2196_);
if (v___x_2199_ == 0)
{
lean_dec(v___y_2196_);
lean_inc(v___y_2198_);
v___y_2189_ = v___y_2195_;
v___y_2190_ = v___y_2198_;
v___y_2191_ = v___y_2197_;
v___y_2192_ = v___y_2198_;
goto v___jp_2188_;
}
else
{
v___y_2189_ = v___y_2195_;
v___y_2190_ = v___y_2198_;
v___y_2191_ = v___y_2197_;
v___y_2192_ = v___y_2196_;
goto v___jp_2188_;
}
}
v___jp_2200_:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = lean_array_get_size(v___y_2201_);
v___x_2203_ = lean_nat_dec_eq(v___x_2202_, v___x_2118_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_sub(v___x_2202_, v___x_2204_);
v___x_2206_ = lean_nat_dec_le(v___x_2118_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_inc(v___x_2205_);
v___y_2195_ = v___x_2202_;
v___y_2196_ = v___x_2205_;
v___y_2197_ = v___y_2201_;
v___y_2198_ = v___x_2205_;
goto v___jp_2194_;
}
else
{
v___y_2195_ = v___x_2202_;
v___y_2196_ = v___x_2205_;
v___y_2197_ = v___y_2201_;
v___y_2198_ = v___x_2118_;
goto v___jp_2194_;
}
}
else
{
v___y_2145_ = v___y_2201_;
goto v___jp_2144_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v___x_2133_);
lean_del_object(v___x_2130_);
lean_dec_ref(v_buckets_2128_);
lean_dec(v_size_2127_);
v_a_2274_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2134_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2134_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v___x_2283_; 
lean_del_object(v___x_2130_);
lean_dec_ref(v_buckets_2128_);
lean_dec(v_size_2127_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_a_2110_);
v___x_2283_ = v___x_2124_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2110_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_a_2110_);
v_a_2287_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2121_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2121_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_ctx_2087_);
v___x_2295_ = 0;
v___x_2296_ = lean_box(v___x_2295_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2296_);
v___x_2298_ = v___x_2112_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2087_);
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_ctx_2087_);
v_a_2302_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2099_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2099_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_Grind_mbtc(v_ctx_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec(v_a_2311_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2323_, lean_object* v_msg_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2323_, v_msg_2324_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2337_, lean_object* v_msg_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2337_, v_msg_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2351_, lean_object* v_m_2352_, lean_object* v_a_2353_, lean_object* v_b_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2352_, v_a_2353_, v_b_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2356_, lean_object* v_m_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2357_, v_a_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2360_, lean_object* v_m_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2360_, v_m_2361_, v_a_2362_);
lean_dec_ref(v_a_2362_);
lean_dec_ref(v_m_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2364_, lean_object* v_val_2365_, lean_object* v___x_2366_, lean_object* v___x_2367_, lean_object* v_as_2368_, lean_object* v_as_x27_2369_, lean_object* v_b_2370_, lean_object* v_a_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2364_, v_val_2365_, v___x_2366_, v___x_2367_, v_as_x27_2369_, v_b_2370_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2384_ = _args[0];
lean_object* v_val_2385_ = _args[1];
lean_object* v___x_2386_ = _args[2];
lean_object* v___x_2387_ = _args[3];
lean_object* v_as_2388_ = _args[4];
lean_object* v_as_x27_2389_ = _args[5];
lean_object* v_b_2390_ = _args[6];
lean_object* v_a_2391_ = _args[7];
lean_object* v___y_2392_ = _args[8];
lean_object* v___y_2393_ = _args[9];
lean_object* v___y_2394_ = _args[10];
lean_object* v___y_2395_ = _args[11];
lean_object* v___y_2396_ = _args[12];
lean_object* v___y_2397_ = _args[13];
lean_object* v___y_2398_ = _args[14];
lean_object* v___y_2399_ = _args[15];
lean_object* v___y_2400_ = _args[16];
lean_object* v___y_2401_ = _args[17];
lean_object* v___y_2402_ = _args[18];
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2384_, v_val_2385_, v___x_2386_, v___x_2387_, v_as_2388_, v_as_x27_2389_, v_b_2390_, v_a_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec(v_as_x27_2389_);
lean_dec(v_as_2388_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2404_, lean_object* v_m_2405_, lean_object* v_a_2406_, lean_object* v_b_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2405_, v_a_2406_, v_b_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2409_, lean_object* v_as_2410_, lean_object* v_lo_2411_, lean_object* v_hi_2412_, lean_object* v_w_2413_, lean_object* v_hlo_2414_, lean_object* v_hhi_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2409_, v_as_2410_, v_lo_2411_, v_hi_2412_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2417_, lean_object* v_as_2418_, lean_object* v_lo_2419_, lean_object* v_hi_2420_, lean_object* v_w_2421_, lean_object* v_hlo_2422_, lean_object* v_hhi_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2417_, v_as_2418_, v_lo_2419_, v_hi_2420_, v_w_2421_, v_hlo_2422_, v_hhi_2423_);
lean_dec(v_hi_2420_);
lean_dec(v_n_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2425_, lean_object* v_a_2426_, lean_object* v_x_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2426_, v_x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2429_, lean_object* v_a_2430_, lean_object* v_x_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2429_, v_a_2430_, v_x_2431_);
lean_dec(v_x_2431_);
lean_dec_ref(v_a_2430_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2434_, lean_object* v_data_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2438_, v_x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2441_, lean_object* v_a_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2441_, v_a_2442_, v_x_2443_);
lean_dec(v_x_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2445_, lean_object* v_a_2446_, lean_object* v_x_2447_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2446_, v_x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2449_, lean_object* v_a_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_res_2452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2449_, v_a_2450_, v_x_2451_);
lean_dec(v_x_2451_);
lean_dec_ref(v_a_2450_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2454_, lean_object* v_data_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2457_, lean_object* v_a_2458_, lean_object* v_b_2459_, lean_object* v_x_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2458_, v_b_2459_, v_x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2462_, lean_object* v_lo_2463_, lean_object* v_hi_2464_, lean_object* v_hhi_2465_, lean_object* v_pivot_2466_, lean_object* v_as_2467_, lean_object* v_i_2468_, lean_object* v_k_2469_, lean_object* v_ilo_2470_, lean_object* v_ik_2471_, lean_object* v_w_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2464_, v_pivot_2466_, v_as_2467_, v_i_2468_, v_k_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2474_, lean_object* v_lo_2475_, lean_object* v_hi_2476_, lean_object* v_hhi_2477_, lean_object* v_pivot_2478_, lean_object* v_as_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_, lean_object* v_ilo_2482_, lean_object* v_ik_2483_, lean_object* v_w_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2474_, v_lo_2475_, v_hi_2476_, v_hhi_2477_, v_pivot_2478_, v_as_2479_, v_i_2480_, v_k_2481_, v_ilo_2482_, v_ik_2483_, v_w_2484_);
lean_dec_ref(v_pivot_2478_);
lean_dec(v_hi_2476_);
lean_dec(v_lo_2475_);
lean_dec(v_n_2474_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2486_, lean_object* v_i_2487_, lean_object* v_source_2488_, lean_object* v_target_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2487_, v_source_2488_, v_target_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2491_, lean_object* v_i_2492_, lean_object* v_source_2493_, lean_object* v_target_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2492_, v_source_2493_, v_target_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2496_, lean_object* v_x_2497_, lean_object* v_x_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2497_, v_x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2501_, v_x_2502_);
return v___x_2503_;
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
