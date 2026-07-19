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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_53_, 1);
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
lean_dec_ref_known(v_x_81_, 2);
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
lean_dec_ref_known(v___x_96_, 1);
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
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_Meta_Sym_canon(v_a_207_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_Meta_Sym_shareCommon(v_a_209_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
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
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object* v_declName_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v_env_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_290_ = lean_st_ref_get(v___y_288_);
v_env_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_env_291_);
lean_dec(v___x_290_);
v___x_292_ = l_Lean_isInstanceReducibleCore(v_env_291_, v_declName_287_);
v___x_293_ = lean_box(v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object* v_declName_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_295_, v___y_296_);
lean_dec(v___y_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object* v_declName_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_299_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object* v_declName_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_304_, v___y_305_, v___y_306_);
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
lean_dec_ref_known(v_f_309_, 2);
v___x_314_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_313_, v_a_311_);
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
lean_dec_ref_known(v___x_341_, 1);
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
lean_dec_ref_known(v_x_365_, 3);
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
lean_object* v___x_935_; lean_object* v_snd_936_; lean_object* v_fst_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1047_; 
v___x_935_ = lean_st_ref_get(v___y_917_);
v_snd_936_ = lean_ctor_get(v_b_916_, 1);
v_fst_937_ = lean_ctor_get(v_b_916_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_b_916_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_939_ = v_b_916_;
v_isShared_940_ = v_isSharedCheck_1047_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_937_);
lean_dec(v_b_916_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1047_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1046_; 
v_fst_941_ = lean_ctor_get(v_snd_936_, 0);
v_snd_942_ = lean_ctor_get(v_snd_936_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_snd_936_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_944_ = v_snd_936_;
v_isShared_945_ = v_isSharedCheck_1046_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_941_);
lean_dec(v_snd_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1046_;
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
lean_object* v_val_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1043_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1043_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_val_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1043_;
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
lean_object* v_options_1007_; uint8_t v_hasTrace_1008_; 
v_options_1007_ = lean_ctor_get(v___y_925_, 2);
v_hasTrace_1008_ = lean_ctor_get_uint8(v_options_1007_, sizeof(void*)*1);
if (v_hasTrace_1008_ == 0)
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
lean_object* v_inheritedTraceOptions_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_inheritedTraceOptions_1009_ = lean_ctor_get(v___y_925_, 13);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1009_, v_options_1007_, v___x_1011_);
if (v___x_1012_ == 0)
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
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_inc(v_val_959_);
v___x_1013_ = l_Lean_MessageData_ofExpr(v_val_959_);
v___x_1014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_inc_ref(v___x_912_);
v___x_1016_ = l_Lean_MessageData_ofExpr(v___x_912_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_inc(v_snd_942_);
v___x_1020_ = l_Nat_reprFast(v_snd_942_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 0, v___x_1020_);
v___x_1022_ = v___x_961_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = l_Lean_MessageData_ofFormat(v___x_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1019_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1010_, v___x_1024_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref_known(v___x_1025_, 1);
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
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_val_959_);
lean_del_object(v___x_944_);
lean_dec(v_snd_942_);
lean_dec(v_fst_941_);
lean_del_object(v___x_939_);
lean_dec(v_fst_937_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctx_911_);
lean_dec_ref(v_e_910_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
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
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
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
v_a_1035_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1004_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1004_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
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
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v___x_958_);
lean_del_object(v___x_944_);
lean_del_object(v___x_939_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_fst_941_);
lean_ctor_set(v___x_1044_, 1, v_snd_942_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_fst_937_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v_a_929_ = v___x_1045_;
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
lean_object* v_e_1048_ = _args[0];
lean_object* v_ctx_1049_ = _args[1];
lean_object* v___x_1050_ = _args[2];
lean_object* v_as_1051_ = _args[3];
lean_object* v_sz_1052_ = _args[4];
lean_object* v_i_1053_ = _args[5];
lean_object* v_b_1054_ = _args[6];
lean_object* v___y_1055_ = _args[7];
lean_object* v___y_1056_ = _args[8];
lean_object* v___y_1057_ = _args[9];
lean_object* v___y_1058_ = _args[10];
lean_object* v___y_1059_ = _args[11];
lean_object* v___y_1060_ = _args[12];
lean_object* v___y_1061_ = _args[13];
lean_object* v___y_1062_ = _args[14];
lean_object* v___y_1063_ = _args[15];
lean_object* v___y_1064_ = _args[16];
lean_object* v___y_1065_ = _args[17];
_start:
{
size_t v_sz_boxed_1066_; size_t v_i_boxed_1067_; lean_object* v_res_1068_; 
v_sz_boxed_1066_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1067_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1048_, v_ctx_1049_, v___x_1050_, v_as_1051_, v_sz_boxed_1066_, v_i_boxed_1067_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v_as_1051_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1069_, lean_object* v_as_1070_, size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_lt(v_i_1072_, v_sz_1071_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v_ctx_1069_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_b_1073_);
return v___x_1086_;
}
else
{
lean_object* v_snd_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1188_; 
v_snd_1087_ = lean_ctor_get(v_b_1073_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_b_1073_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_b_1073_, 0);
lean_dec(v_unused_1189_);
v___x_1089_ = v_b_1073_;
v_isShared_1090_ = v_isSharedCheck_1188_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1087_);
lean_dec(v_b_1073_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1188_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1187_; 
v_fst_1091_ = lean_ctor_get(v_snd_1087_, 0);
v_snd_1092_ = lean_ctor_get(v_snd_1087_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_snd_1087_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1094_ = v_snd_1087_;
v_isShared_1095_ = v_isSharedCheck_1187_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_snd_1092_);
lean_inc(v_fst_1091_);
lean_dec(v_snd_1087_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1187_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v_a_1098_; lean_object* v_a_1111_; uint8_t v___y_1113_; uint8_t v___x_1185_; 
v___x_1096_ = lean_box(0);
v_a_1111_ = lean_array_uget_borrowed(v_as_1070_, v_i_1072_);
v___x_1185_ = l_Lean_Expr_isApp(v_a_1111_);
if (v___x_1185_ == 0)
{
v___y_1113_ = v___x_1185_;
goto v___jp_1112_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = l_Lean_Expr_isEq(v_a_1111_);
if (v___x_1186_ == 0)
{
v___y_1113_ = v___x_1185_;
goto v___jp_1112_;
}
else
{
goto v___jp_1105_;
}
}
v___jp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_a_1098_);
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1098_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
size_t v___x_1101_; size_t v___x_1102_; 
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1072_, v___x_1101_);
v_i_1072_ = v___x_1102_;
v_b_1073_ = v___x_1100_;
goto _start;
}
}
v___jp_1105_:
{
lean_object* v___x_1107_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_snd_1092_);
lean_ctor_set(v___x_1089_, 0, v_fst_1091_);
v___x_1107_ = v___x_1089_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1091_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_snd_1092_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v_a_1098_ = v___x_1107_;
goto v___jp_1097_;
}
}
v___jp_1109_:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_fst_1091_);
lean_ctor_set(v___x_1110_, 1, v_snd_1092_);
v_a_1098_ = v___x_1110_;
goto v___jp_1097_;
}
v___jp_1112_:
{
if (v___y_1113_ == 0)
{
goto v___jp_1105_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Expr_isHEq(v_a_1111_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_del_object(v___x_1089_);
lean_inc(v_a_1111_);
v___x_1115_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1111_, v___y_1074_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_unbox(v_a_1116_);
lean_dec(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_fst_1091_);
lean_ctor_set(v___x_1118_, 1, v_snd_1092_);
v_a_1098_ = v___x_1118_;
goto v___jp_1097_;
}
else
{
lean_object* v_isInterpreted_1119_; lean_object* v___x_1120_; 
v_isInterpreted_1119_ = lean_ctor_get(v_ctx_1069_, 0);
lean_inc_ref(v_isInterpreted_1119_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc(v_a_1111_);
v___x_1120_ = lean_apply_12(v_isInterpreted_1119_, v_a_1111_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; uint8_t v___x_1122_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = lean_unbox(v_a_1121_);
lean_dec(v_a_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Lean_Expr_getAppFn(v_a_1111_);
lean_inc_ref(v___x_1123_);
v___x_1124_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1123_, v___y_1082_, v___y_1083_);
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
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1123_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_dummy_1129_; lean_object* v_nargs_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v_dummy_1129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1130_ = l_Lean_Expr_getAppNumArgs(v_a_1111_);
lean_inc(v_nargs_1130_);
v___x_1131_ = lean_mk_array(v_nargs_1130_, v_dummy_1129_);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_sub(v_nargs_1130_, v___x_1132_);
lean_dec(v_nargs_1130_);
lean_inc_n(v_a_1111_, 2);
v___x_1134_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1111_, v___x_1131_, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_snd_1092_);
lean_ctor_set(v___x_1135_, 1, v___x_1128_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_fst_1091_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v_sz_1137_ = lean_array_size(v___x_1134_);
v___x_1138_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1069_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1111_, v_ctx_1069_, v___x_1123_, v___x_1134_, v_sz_1137_, v___x_1138_, v___x_1136_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref(v___x_1134_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v_snd_1141_; lean_object* v_fst_1142_; lean_object* v_fst_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v_snd_1141_ = lean_ctor_get(v_a_1140_, 1);
lean_inc(v_snd_1141_);
v_fst_1142_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_fst_1142_);
lean_dec(v_a_1140_);
v_fst_1143_ = lean_ctor_get(v_snd_1141_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_snd_1141_, 1);
lean_dec(v_unused_1151_);
v___x_1145_ = v_snd_1141_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_fst_1143_);
lean_dec(v_snd_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_fst_1143_);
lean_ctor_set(v___x_1145_, 0, v_fst_1142_);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fst_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_fst_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
v_a_1098_ = v___x_1148_;
goto v___jp_1097_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1094_);
lean_dec_ref(v_ctx_1069_);
v_a_1152_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1139_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1139_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_dec_ref(v___x_1123_);
goto v___jp_1109_;
}
}
else
{
lean_dec_ref(v___x_1123_);
goto v___jp_1109_;
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v___x_1123_);
lean_del_object(v___x_1094_);
lean_dec(v_snd_1092_);
lean_dec(v_fst_1091_);
lean_dec_ref(v_ctx_1069_);
v_a_1160_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1124_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1124_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_fst_1091_);
lean_ctor_set(v___x_1168_, 1, v_snd_1092_);
v_a_1098_ = v___x_1168_;
goto v___jp_1097_;
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_del_object(v___x_1094_);
lean_dec(v_snd_1092_);
lean_dec(v_fst_1091_);
lean_dec_ref(v_ctx_1069_);
v_a_1169_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1120_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1120_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_del_object(v___x_1094_);
lean_dec(v_snd_1092_);
lean_dec(v_fst_1091_);
lean_dec_ref(v_ctx_1069_);
v_a_1177_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1115_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1115_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
goto v___jp_1105_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object* v_ctx_1190_, lean_object* v_as_1191_, lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1190_, v_as_1191_, v_sz_boxed_1206_, v_i_boxed_1207_, v_b_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v_as_1191_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1209_, lean_object* v_as_1210_, size_t v_sz_1211_, size_t v_i_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_lt(v_i_1212_, v_sz_1211_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_ctx_1209_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_b_1213_);
return v___x_1226_;
}
else
{
lean_object* v_snd_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1328_; 
v_snd_1227_ = lean_ctor_get(v_b_1213_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_b_1213_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_b_1213_, 0);
lean_dec(v_unused_1329_);
v___x_1229_ = v_b_1213_;
v_isShared_1230_ = v_isSharedCheck_1328_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snd_1227_);
lean_dec(v_b_1213_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1328_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_fst_1231_; lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1327_; 
v_fst_1231_ = lean_ctor_get(v_snd_1227_, 0);
v_snd_1232_ = lean_ctor_get(v_snd_1227_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1227_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1234_ = v_snd_1227_;
v_isShared_1235_ = v_isSharedCheck_1327_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_inc(v_fst_1231_);
lean_dec(v_snd_1227_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1327_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v_a_1238_; lean_object* v_a_1251_; uint8_t v___y_1253_; uint8_t v___x_1325_; 
v___x_1236_ = lean_box(0);
v_a_1251_ = lean_array_uget_borrowed(v_as_1210_, v_i_1212_);
v___x_1325_ = l_Lean_Expr_isApp(v_a_1251_);
if (v___x_1325_ == 0)
{
v___y_1253_ = v___x_1325_;
goto v___jp_1252_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Expr_isEq(v_a_1251_);
if (v___x_1326_ == 0)
{
v___y_1253_ = v___x_1325_;
goto v___jp_1252_;
}
else
{
goto v___jp_1245_;
}
}
v___jp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_a_1238_);
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1240_ = v___x_1234_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_a_1238_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1212_, v___x_1241_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1209_, v_as_1210_, v_sz_1211_, v___x_1242_, v___x_1240_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1243_;
}
}
v___jp_1245_:
{
lean_object* v___x_1247_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_snd_1232_);
lean_ctor_set(v___x_1229_, 0, v_fst_1231_);
v___x_1247_ = v___x_1229_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_fst_1231_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_snd_1232_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
v_a_1238_ = v___x_1247_;
goto v___jp_1237_;
}
}
v___jp_1249_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_fst_1231_);
lean_ctor_set(v___x_1250_, 1, v_snd_1232_);
v_a_1238_ = v___x_1250_;
goto v___jp_1237_;
}
v___jp_1252_:
{
if (v___y_1253_ == 0)
{
goto v___jp_1245_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Lean_Expr_isHEq(v_a_1251_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1229_);
lean_inc(v_a_1251_);
v___x_1255_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1251_, v___y_1214_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; uint8_t v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = lean_unbox(v_a_1256_);
lean_dec(v_a_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_fst_1231_);
lean_ctor_set(v___x_1258_, 1, v_snd_1232_);
v_a_1238_ = v___x_1258_;
goto v___jp_1237_;
}
else
{
lean_object* v_isInterpreted_1259_; lean_object* v___x_1260_; 
v_isInterpreted_1259_ = lean_ctor_get(v_ctx_1209_, 0);
lean_inc_ref(v_isInterpreted_1259_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v_a_1251_);
v___x_1260_ = lean_apply_12(v_isInterpreted_1259_, v_a_1251_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
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
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = l_Lean_Expr_getAppFn(v_a_1251_);
lean_inc_ref(v___x_1263_);
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1263_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; uint8_t v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1263_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v_dummy_1269_; lean_object* v_nargs_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1268_ = lean_unsigned_to_nat(0u);
v_dummy_1269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1270_ = l_Lean_Expr_getAppNumArgs(v_a_1251_);
lean_inc(v_nargs_1270_);
v___x_1271_ = lean_mk_array(v_nargs_1270_, v_dummy_1269_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_sub(v_nargs_1270_, v___x_1272_);
lean_dec(v_nargs_1270_);
lean_inc_n(v_a_1251_, 2);
v___x_1274_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1251_, v___x_1271_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_snd_1232_);
lean_ctor_set(v___x_1275_, 1, v___x_1268_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_fst_1231_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v_sz_1277_ = lean_array_size(v___x_1274_);
v___x_1278_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1209_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1251_, v_ctx_1209_, v___x_1263_, v___x_1274_, v_sz_1277_, v___x_1278_, v___x_1276_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_snd_1281_; lean_object* v_fst_1282_; lean_object* v_fst_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v_snd_1281_ = lean_ctor_get(v_a_1280_, 1);
lean_inc(v_snd_1281_);
v_fst_1282_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_fst_1282_);
lean_dec(v_a_1280_);
v_fst_1283_ = lean_ctor_get(v_snd_1281_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_snd_1281_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_snd_1281_, 1);
lean_dec(v_unused_1291_);
v___x_1285_ = v_snd_1281_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_fst_1283_);
lean_dec(v_snd_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_fst_1283_);
lean_ctor_set(v___x_1285_, 0, v_fst_1282_);
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_fst_1282_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_fst_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v_a_1238_ = v___x_1288_;
goto v___jp_1237_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_del_object(v___x_1234_);
lean_dec_ref(v_ctx_1209_);
v_a_1292_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1279_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1279_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_dec_ref(v___x_1263_);
goto v___jp_1249_;
}
}
else
{
lean_dec_ref(v___x_1263_);
goto v___jp_1249_;
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v___x_1263_);
lean_del_object(v___x_1234_);
lean_dec(v_snd_1232_);
lean_dec(v_fst_1231_);
lean_dec_ref(v_ctx_1209_);
v_a_1300_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1264_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1264_);
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
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_fst_1231_);
lean_ctor_set(v___x_1308_, 1, v_snd_1232_);
v_a_1238_ = v___x_1308_;
goto v___jp_1237_;
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_del_object(v___x_1234_);
lean_dec(v_snd_1232_);
lean_dec(v_fst_1231_);
lean_dec_ref(v_ctx_1209_);
v_a_1309_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1260_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1260_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1234_);
lean_dec(v_snd_1232_);
lean_dec(v_fst_1231_);
lean_dec_ref(v_ctx_1209_);
v_a_1317_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1255_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1255_);
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
else
{
goto v___jp_1245_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object* v_ctx_1330_, lean_object* v_as_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
size_t v_sz_boxed_1346_; size_t v_i_boxed_1347_; lean_object* v_res_1348_; 
v_sz_boxed_1346_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1330_, v_as_1331_, v_sz_boxed_1346_, v_i_boxed_1347_, v_b_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v_as_1331_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1349_, lean_object* v_as_1350_, size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v_ctx_1349_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_b_1353_);
return v___x_1366_;
}
else
{
lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1468_; 
v_snd_1367_ = lean_ctor_get(v_b_1353_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_b_1353_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_b_1353_, 0);
lean_dec(v_unused_1469_);
v___x_1369_ = v_b_1353_;
v_isShared_1370_ = v_isSharedCheck_1468_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_dec(v_b_1353_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1468_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1467_; 
v_fst_1371_ = lean_ctor_get(v_snd_1367_, 0);
v_snd_1372_ = lean_ctor_get(v_snd_1367_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_snd_1367_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1374_ = v_snd_1367_;
v_isShared_1375_ = v_isSharedCheck_1467_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_snd_1367_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1467_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v_a_1378_; lean_object* v_a_1391_; uint8_t v___y_1393_; uint8_t v___x_1465_; 
v___x_1376_ = lean_box(0);
v_a_1391_ = lean_array_uget_borrowed(v_as_1350_, v_i_1352_);
v___x_1465_ = l_Lean_Expr_isApp(v_a_1391_);
if (v___x_1465_ == 0)
{
v___y_1393_ = v___x_1465_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = l_Lean_Expr_isEq(v_a_1391_);
if (v___x_1466_ == 0)
{
v___y_1393_ = v___x_1465_;
goto v___jp_1392_;
}
else
{
goto v___jp_1385_;
}
}
v___jp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_a_1378_);
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1380_ = v___x_1374_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_a_1378_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
size_t v___x_1381_; size_t v___x_1382_; 
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1352_, v___x_1381_);
v_i_1352_ = v___x_1382_;
v_b_1353_ = v___x_1380_;
goto _start;
}
}
v___jp_1385_:
{
lean_object* v___x_1387_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_snd_1372_);
lean_ctor_set(v___x_1369_, 0, v_fst_1371_);
v___x_1387_ = v___x_1369_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_fst_1371_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_snd_1372_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
v_a_1378_ = v___x_1387_;
goto v___jp_1377_;
}
}
v___jp_1389_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_fst_1371_);
lean_ctor_set(v___x_1390_, 1, v_snd_1372_);
v_a_1378_ = v___x_1390_;
goto v___jp_1377_;
}
v___jp_1392_:
{
if (v___y_1393_ == 0)
{
goto v___jp_1385_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Lean_Expr_isHEq(v_a_1391_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_del_object(v___x_1369_);
lean_inc(v_a_1391_);
v___x_1395_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1391_, v___y_1354_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; uint8_t v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_unbox(v_a_1396_);
lean_dec(v_a_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_fst_1371_);
lean_ctor_set(v___x_1398_, 1, v_snd_1372_);
v_a_1378_ = v___x_1398_;
goto v___jp_1377_;
}
else
{
lean_object* v_isInterpreted_1399_; lean_object* v___x_1400_; 
v_isInterpreted_1399_ = lean_ctor_get(v_ctx_1349_, 0);
lean_inc_ref(v_isInterpreted_1399_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v_a_1391_);
v___x_1400_ = lean_apply_12(v_isInterpreted_1399_, v_a_1391_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, lean_box(0));
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; uint8_t v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = lean_unbox(v_a_1401_);
lean_dec(v_a_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_Lean_Expr_getAppFn(v_a_1391_);
lean_inc_ref(v___x_1403_);
v___x_1404_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1403_, v___y_1362_, v___y_1363_);
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
uint8_t v___x_1407_; 
v___x_1407_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1403_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v_dummy_1409_; lean_object* v_nargs_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v_dummy_1409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1410_ = l_Lean_Expr_getAppNumArgs(v_a_1391_);
lean_inc(v_nargs_1410_);
v___x_1411_ = lean_mk_array(v_nargs_1410_, v_dummy_1409_);
v___x_1412_ = lean_unsigned_to_nat(1u);
v___x_1413_ = lean_nat_sub(v_nargs_1410_, v___x_1412_);
lean_dec(v_nargs_1410_);
lean_inc_n(v_a_1391_, 2);
v___x_1414_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1391_, v___x_1411_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_snd_1372_);
lean_ctor_set(v___x_1415_, 1, v___x_1408_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_fst_1371_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v_sz_1417_ = lean_array_size(v___x_1414_);
v___x_1418_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1349_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1391_, v_ctx_1349_, v___x_1403_, v___x_1414_, v_sz_1417_, v___x_1418_, v___x_1416_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec_ref(v___x_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_snd_1421_; lean_object* v_fst_1422_; lean_object* v_fst_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v_snd_1421_ = lean_ctor_get(v_a_1420_, 1);
lean_inc(v_snd_1421_);
v_fst_1422_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_fst_1422_);
lean_dec(v_a_1420_);
v_fst_1423_ = lean_ctor_get(v_snd_1421_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_snd_1421_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_snd_1421_, 1);
lean_dec(v_unused_1431_);
v___x_1425_ = v_snd_1421_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_fst_1423_);
lean_dec(v_snd_1421_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v_fst_1423_);
lean_ctor_set(v___x_1425_, 0, v_fst_1422_);
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_fst_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_fst_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
v_a_1378_ = v___x_1428_;
goto v___jp_1377_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1374_);
lean_dec_ref(v_ctx_1349_);
v_a_1432_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1419_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1419_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_dec_ref(v___x_1403_);
goto v___jp_1389_;
}
}
else
{
lean_dec_ref(v___x_1403_);
goto v___jp_1389_;
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1403_);
lean_del_object(v___x_1374_);
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
lean_dec_ref(v_ctx_1349_);
v_a_1440_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1404_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1404_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_fst_1371_);
lean_ctor_set(v___x_1448_, 1, v_snd_1372_);
v_a_1378_ = v___x_1448_;
goto v___jp_1377_;
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1374_);
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
lean_dec_ref(v_ctx_1349_);
v_a_1449_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1400_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1400_);
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
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1374_);
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
lean_dec_ref(v_ctx_1349_);
v_a_1457_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1395_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1395_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
else
{
goto v___jp_1385_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object* v_ctx_1470_, lean_object* v_as_1471_, lean_object* v_sz_1472_, lean_object* v_i_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
size_t v_sz_boxed_1486_; size_t v_i_boxed_1487_; lean_object* v_res_1488_; 
v_sz_boxed_1486_ = lean_unbox_usize(v_sz_1472_);
lean_dec(v_sz_1472_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1470_, v_as_1471_, v_sz_boxed_1486_, v_i_boxed_1487_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v_as_1471_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1489_, lean_object* v_as_1490_, size_t v_sz_1491_, size_t v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1492_, v_sz_1491_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v_ctx_1489_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_b_1493_);
return v___x_1506_;
}
else
{
lean_object* v_snd_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1608_; 
v_snd_1507_ = lean_ctor_get(v_b_1493_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_b_1493_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_b_1493_, 0);
lean_dec(v_unused_1609_);
v___x_1509_ = v_b_1493_;
v_isShared_1510_ = v_isSharedCheck_1608_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1507_);
lean_dec(v_b_1493_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1608_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1607_; 
v_fst_1511_ = lean_ctor_get(v_snd_1507_, 0);
v_snd_1512_ = lean_ctor_get(v_snd_1507_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_snd_1507_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1514_ = v_snd_1507_;
v_isShared_1515_ = v_isSharedCheck_1607_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_snd_1507_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1607_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v_a_1518_; lean_object* v_a_1531_; uint8_t v___y_1533_; uint8_t v___x_1605_; 
v___x_1516_ = lean_box(0);
v_a_1531_ = lean_array_uget_borrowed(v_as_1490_, v_i_1492_);
v___x_1605_ = l_Lean_Expr_isApp(v_a_1531_);
if (v___x_1605_ == 0)
{
v___y_1533_ = v___x_1605_;
goto v___jp_1532_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Expr_isEq(v_a_1531_);
if (v___x_1606_ == 0)
{
v___y_1533_ = v___x_1605_;
goto v___jp_1532_;
}
else
{
goto v___jp_1525_;
}
}
v___jp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_a_1518_);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1492_, v___x_1521_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1489_, v_as_1490_, v_sz_1491_, v___x_1522_, v___x_1520_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
return v___x_1523_;
}
}
v___jp_1525_:
{
lean_object* v___x_1527_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_snd_1512_);
lean_ctor_set(v___x_1509_, 0, v_fst_1511_);
v___x_1527_ = v___x_1509_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_fst_1511_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_snd_1512_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_a_1518_ = v___x_1527_;
goto v___jp_1517_;
}
}
v___jp_1529_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_fst_1511_);
lean_ctor_set(v___x_1530_, 1, v_snd_1512_);
v_a_1518_ = v___x_1530_;
goto v___jp_1517_;
}
v___jp_1532_:
{
if (v___y_1533_ == 0)
{
goto v___jp_1525_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_Expr_isHEq(v_a_1531_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_del_object(v___x_1509_);
lean_inc(v_a_1531_);
v___x_1535_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1531_, v___y_1494_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; uint8_t v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = lean_unbox(v_a_1536_);
lean_dec(v_a_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_fst_1511_);
lean_ctor_set(v___x_1538_, 1, v_snd_1512_);
v_a_1518_ = v___x_1538_;
goto v___jp_1517_;
}
else
{
lean_object* v_isInterpreted_1539_; lean_object* v___x_1540_; 
v_isInterpreted_1539_ = lean_ctor_get(v_ctx_1489_, 0);
lean_inc_ref(v_isInterpreted_1539_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc(v_a_1531_);
v___x_1540_ = lean_apply_12(v_isInterpreted_1539_, v_a_1531_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, lean_box(0));
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; uint8_t v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = lean_unbox(v_a_1541_);
lean_dec(v_a_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = l_Lean_Expr_getAppFn(v_a_1531_);
lean_inc_ref(v___x_1543_);
v___x_1544_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1543_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; uint8_t v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1543_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v_dummy_1549_; lean_object* v_nargs_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; size_t v_sz_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v_dummy_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1550_ = l_Lean_Expr_getAppNumArgs(v_a_1531_);
lean_inc(v_nargs_1550_);
v___x_1551_ = lean_mk_array(v_nargs_1550_, v_dummy_1549_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_sub(v_nargs_1550_, v___x_1552_);
lean_dec(v_nargs_1550_);
lean_inc_n(v_a_1531_, 2);
v___x_1554_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1531_, v___x_1551_, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_snd_1512_);
lean_ctor_set(v___x_1555_, 1, v___x_1548_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_fst_1511_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v_sz_1557_ = lean_array_size(v___x_1554_);
v___x_1558_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1489_);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1531_, v_ctx_1489_, v___x_1543_, v___x_1554_, v_sz_1557_, v___x_1558_, v___x_1556_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec_ref(v___x_1554_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_snd_1561_; lean_object* v_fst_1562_; lean_object* v_fst_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v_snd_1561_ = lean_ctor_get(v_a_1560_, 1);
lean_inc(v_snd_1561_);
v_fst_1562_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_fst_1562_);
lean_dec(v_a_1560_);
v_fst_1563_ = lean_ctor_get(v_snd_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_snd_1561_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_snd_1561_, 1);
lean_dec(v_unused_1571_);
v___x_1565_ = v_snd_1561_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_fst_1563_);
lean_dec(v_snd_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v_fst_1563_);
lean_ctor_set(v___x_1565_, 0, v_fst_1562_);
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_fst_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_fst_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
v_a_1518_ = v___x_1568_;
goto v___jp_1517_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1514_);
lean_dec_ref(v_ctx_1489_);
v_a_1572_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1559_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1559_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_dec_ref(v___x_1543_);
goto v___jp_1529_;
}
}
else
{
lean_dec_ref(v___x_1543_);
goto v___jp_1529_;
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___x_1543_);
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec_ref(v_ctx_1489_);
v_a_1580_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1544_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1544_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_fst_1511_);
lean_ctor_set(v___x_1588_, 1, v_snd_1512_);
v_a_1518_ = v___x_1588_;
goto v___jp_1517_;
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec_ref(v_ctx_1489_);
v_a_1589_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1540_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1540_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec_ref(v_ctx_1489_);
v_a_1597_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1535_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1535_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
goto v___jp_1525_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object* v_ctx_1610_, lean_object* v_as_1611_, lean_object* v_sz_1612_, lean_object* v_i_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
size_t v_sz_boxed_1626_; size_t v_i_boxed_1627_; lean_object* v_res_1628_; 
v_sz_boxed_1626_ = lean_unbox_usize(v_sz_1612_);
lean_dec(v_sz_1612_);
v_i_boxed_1627_ = lean_unbox_usize(v_i_1613_);
lean_dec(v_i_1613_);
v_res_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1610_, v_as_1611_, v_sz_boxed_1626_, v_i_boxed_1627_, v_b_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v_as_1611_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1629_, lean_object* v_ctx_1630_, lean_object* v_n_1631_, lean_object* v_b_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
if (lean_obj_tag(v_n_1631_) == 0)
{
lean_object* v_cs_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v_cs_1644_ = lean_ctor_get(v_n_1631_, 0);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_b_1632_);
v_sz_1647_ = lean_array_size(v_cs_1644_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1629_, v_ctx_1630_, v_cs_1644_, v_sz_1647_, v___x_1648_, v___x_1646_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1664_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1664_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1664_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_fst_1654_; 
v_fst_1654_ = lean_ctor_get(v_a_1650_, 0);
if (lean_obj_tag(v_fst_1654_) == 0)
{
lean_object* v_snd_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v_snd_1655_ = lean_ctor_get(v_a_1650_, 1);
lean_inc(v_snd_1655_);
lean_dec(v_a_1650_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_snd_1655_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1656_);
v___x_1658_ = v___x_1652_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v_val_1660_; lean_object* v___x_1662_; 
lean_inc_ref(v_fst_1654_);
lean_dec(v_a_1650_);
v_val_1660_ = lean_ctor_get(v_fst_1654_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v_fst_1654_, 1);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_val_1660_);
v___x_1662_ = v___x_1652_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_val_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1649_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1649_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_vs_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v_vs_1673_ = lean_ctor_get(v_n_1631_, 0);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_b_1632_);
v_sz_1676_ = lean_array_size(v_vs_1673_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1630_, v_vs_1673_, v_sz_1676_, v___x_1677_, v___x_1675_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1693_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_fst_1683_; 
v_fst_1683_ = lean_ctor_get(v_a_1679_, 0);
if (lean_obj_tag(v_fst_1683_) == 0)
{
lean_object* v_snd_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v_snd_1684_ = lean_ctor_get(v_a_1679_, 1);
lean_inc(v_snd_1684_);
lean_dec(v_a_1679_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_snd_1684_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1685_);
v___x_1687_ = v___x_1681_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v_val_1689_; lean_object* v___x_1691_; 
lean_inc_ref(v_fst_1683_);
lean_dec(v_a_1679_);
v_val_1689_ = lean_ctor_get(v_fst_1683_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v_fst_1683_, 1);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_val_1689_);
v___x_1691_ = v___x_1681_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_val_1689_);
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
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1678_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1678_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1702_, lean_object* v_ctx_1703_, lean_object* v_as_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref(v_ctx_1703_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1707_);
return v___x_1720_;
}
else
{
lean_object* v_snd_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1755_; 
v_snd_1721_ = lean_ctor_get(v_b_1707_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_b_1707_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_b_1707_, 0);
lean_dec(v_unused_1756_);
v___x_1723_ = v_b_1707_;
v_isShared_1724_ = v_isSharedCheck_1755_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_snd_1721_);
lean_dec(v_b_1707_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1755_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_array_uget_borrowed(v_as_1704_, v_i_1706_);
lean_inc(v_snd_1721_);
lean_inc_ref(v_ctx_1703_);
v___x_1726_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1702_, v_ctx_1703_, v_a_1725_, v_snd_1721_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1746_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1746_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1746_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
if (lean_obj_tag(v_a_1727_) == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec_ref(v_ctx_1703_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1727_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1731_);
v___x_1733_ = v___x_1723_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_snd_1721_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1733_);
v___x_1735_ = v___x_1729_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_del_object(v___x_1729_);
lean_dec(v_snd_1721_);
v_a_1738_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v_a_1727_, 1);
v___x_1739_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v_a_1738_);
lean_ctor_set(v___x_1723_, 0, v___x_1739_);
v___x_1741_ = v___x_1723_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1738_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
size_t v___x_1742_; size_t v___x_1743_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1706_, v___x_1742_);
v_i_1706_ = v___x_1743_;
v_b_1707_ = v___x_1741_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1723_);
lean_dec(v_snd_1721_);
lean_dec_ref(v_ctx_1703_);
v_a_1747_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1726_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1726_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1757_ = _args[0];
lean_object* v_ctx_1758_ = _args[1];
lean_object* v_as_1759_ = _args[2];
lean_object* v_sz_1760_ = _args[3];
lean_object* v_i_1761_ = _args[4];
lean_object* v_b_1762_ = _args[5];
lean_object* v___y_1763_ = _args[6];
lean_object* v___y_1764_ = _args[7];
lean_object* v___y_1765_ = _args[8];
lean_object* v___y_1766_ = _args[9];
lean_object* v___y_1767_ = _args[10];
lean_object* v___y_1768_ = _args[11];
lean_object* v___y_1769_ = _args[12];
lean_object* v___y_1770_ = _args[13];
lean_object* v___y_1771_ = _args[14];
lean_object* v___y_1772_ = _args[15];
lean_object* v___y_1773_ = _args[16];
_start:
{
size_t v_sz_boxed_1774_; size_t v_i_boxed_1775_; lean_object* v_res_1776_; 
v_sz_boxed_1774_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1775_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1757_, v_ctx_1758_, v_as_1759_, v_sz_boxed_1774_, v_i_boxed_1775_, v_b_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v_as_1759_);
lean_dec_ref(v_init_1757_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1777_, lean_object* v_ctx_1778_, lean_object* v_n_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1777_, v_ctx_1778_, v_n_1779_, v_b_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v_n_1779_);
lean_dec_ref(v_init_1777_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1793_, lean_object* v_t_1794_, lean_object* v_init_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_root_1807_; lean_object* v_tail_1808_; lean_object* v___x_1809_; 
v_root_1807_ = lean_ctor_get(v_t_1794_, 0);
v_tail_1808_ = lean_ctor_get(v_t_1794_, 1);
lean_inc_ref(v_ctx_1793_);
lean_inc_ref(v_init_1795_);
v___x_1809_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1795_, v_ctx_1793_, v_root_1807_, v_init_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_init_1795_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1846_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1846_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1846_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
if (lean_obj_tag(v_a_1810_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; 
lean_dec_ref(v_ctx_1793_);
v_a_1814_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v_a_1810_, 1);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v_a_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; size_t v_sz_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
lean_del_object(v___x_1812_);
v_a_1818_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v_a_1810_, 1);
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_a_1818_);
v_sz_1821_ = lean_array_size(v_tail_1808_);
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1793_, v_tail_1808_, v_sz_1821_, v___x_1822_, v___x_1820_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1837_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1837_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1837_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_fst_1828_; 
v_fst_1828_ = lean_ctor_get(v_a_1824_, 0);
if (lean_obj_tag(v_fst_1828_) == 0)
{
lean_object* v_snd_1829_; lean_object* v___x_1831_; 
v_snd_1829_ = lean_ctor_get(v_a_1824_, 1);
lean_inc(v_snd_1829_);
lean_dec(v_a_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_snd_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_snd_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1835_; 
lean_inc_ref(v_fst_1828_);
lean_dec(v_a_1824_);
v_val_1833_ = lean_ctor_get(v_fst_1828_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_fst_1828_, 1);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_val_1833_);
v___x_1835_ = v___x_1826_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_val_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1823_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1823_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_ctx_1793_);
v_a_1847_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1809_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1809_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1855_, lean_object* v_t_1856_, lean_object* v_init_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1855_, v_t_1856_, v_init_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v_t_1856_);
return v_res_1869_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1875_ = l_Lean_Name_append(v___x_1874_, v___x_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1876_, size_t v_i_1877_, size_t v_stop_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_a_1892_; uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_eq(v_i_1877_, v_stop_1878_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_array_uget_borrowed(v_as_1876_, v_i_1877_);
v___x_1898_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1897_, v___y_1880_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; uint8_t v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = lean_unbox(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1900_ == 0)
{
if (lean_obj_tag(v___x_1897_) == 2)
{
lean_object* v_a_1901_; lean_object* v_b_1902_; lean_object* v_eq_1903_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v_options_1959_; uint8_t v_hasTrace_1960_; 
v_a_1901_ = lean_ctor_get(v___x_1897_, 0);
v_b_1902_ = lean_ctor_get(v___x_1897_, 1);
v_eq_1903_ = lean_ctor_get(v___x_1897_, 3);
v_options_1959_ = lean_ctor_get(v___y_1888_, 2);
v_hasTrace_1960_ = lean_ctor_get_uint8(v_options_1959_, sizeof(void*)*1);
if (v_hasTrace_1960_ == 0)
{
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
v___y_1937_ = v___y_1889_;
goto v___jp_1927_;
}
else
{
lean_object* v_inheritedTraceOptions_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_inheritedTraceOptions_1961_ = lean_ctor_get(v___y_1888_, 13);
v___x_1962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1963_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1961_, v_options_1959_, v___x_1963_);
if (v___x_1964_ == 0)
{
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
v___y_1937_ = v___y_1889_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_inc_ref(v_eq_1903_);
v___x_1965_ = l_Lean_MessageData_ofExpr(v_eq_1903_);
v___x_1966_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1962_, v___x_1965_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_dec_ref_known(v___x_1966_, 1);
v___y_1928_ = v___y_1880_;
v___y_1929_ = v___y_1881_;
v___y_1930_ = v___y_1882_;
v___y_1931_ = v___y_1883_;
v___y_1932_ = v___y_1884_;
v___y_1933_ = v___y_1885_;
v___y_1934_ = v___y_1886_;
v___y_1935_ = v___y_1887_;
v___y_1936_ = v___y_1888_;
v___y_1937_ = v___y_1889_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_b_1879_);
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
v___jp_1904_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_box(0);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1908_);
lean_inc(v___y_1909_);
lean_inc_ref(v_eq_1903_);
v___x_1917_ = lean_grind_internalize(v_eq_1903_, v___y_1915_, v___x_1916_, v___y_1909_, v___y_1908_, v___y_1914_, v___y_1906_, v___y_1913_, v___y_1910_, v___y_1905_, v___y_1911_, v___y_1907_, v___y_1912_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref_known(v___x_1917_, 1);
lean_inc_ref(v___x_1897_);
v___x_1918_ = lean_array_push(v_b_1879_, v___x_1897_);
v_a_1892_ = v___x_1918_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_b_1879_);
v_a_1919_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1917_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
v___jp_1927_:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1901_, v___y_1928_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1902_, v___y_1928_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; uint8_t v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = lean_nat_dec_le(v_a_1939_, v_a_1941_);
if (v___x_1942_ == 0)
{
lean_dec(v_a_1941_);
v___y_1905_ = v___y_1934_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___y_1929_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___y_1933_;
v___y_1911_ = v___y_1935_;
v___y_1912_ = v___y_1937_;
v___y_1913_ = v___y_1932_;
v___y_1914_ = v___y_1930_;
v___y_1915_ = v_a_1939_;
goto v___jp_1904_;
}
else
{
lean_dec(v_a_1939_);
v___y_1905_ = v___y_1934_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___y_1929_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___y_1933_;
v___y_1911_ = v___y_1935_;
v___y_1912_ = v___y_1937_;
v___y_1913_ = v___y_1932_;
v___y_1914_ = v___y_1930_;
v___y_1915_ = v_a_1941_;
goto v___jp_1904_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_a_1939_);
lean_dec_ref(v_b_1879_);
v_a_1943_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1940_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1940_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_b_1879_);
v_a_1951_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1938_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1938_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
v_a_1892_ = v_b_1879_;
goto v___jp_1891_;
}
}
else
{
v_a_1892_ = v_b_1879_;
goto v___jp_1891_;
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_b_1879_);
v_a_1975_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1898_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1898_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_b_1879_);
return v___x_1983_;
}
v___jp_1891_:
{
size_t v___x_1893_; size_t v___x_1894_; 
v___x_1893_ = ((size_t)1ULL);
v___x_1894_ = lean_usize_add(v_i_1877_, v___x_1893_);
v_i_1877_ = v___x_1894_;
v_b_1879_ = v_a_1892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_stop_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
size_t v_i_boxed_1999_; size_t v_stop_boxed_2000_; lean_object* v_res_2001_; 
v_i_boxed_1999_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_stop_boxed_2000_ = lean_unbox_usize(v_stop_1986_);
lean_dec(v_stop_1986_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_1984_, v_i_boxed_1999_, v_stop_boxed_2000_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_as_1984_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2004_, lean_object* v_start_2005_, lean_object* v_stop_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2019_ = lean_nat_dec_lt(v_start_2005_, v_stop_2006_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2018_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_array_get_size(v_as_2004_);
v___x_2022_ = lean_nat_dec_le(v_stop_2006_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_nat_dec_lt(v_start_2005_, v___x_2021_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2018_);
return v___x_2024_;
}
else
{
size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = lean_usize_of_nat(v_start_2005_);
v___x_2026_ = lean_usize_of_nat(v___x_2021_);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2004_, v___x_2025_, v___x_2026_, v___x_2018_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2027_;
}
}
else
{
size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_usize_of_nat(v_start_2005_);
v___x_2029_ = lean_usize_of_nat(v_stop_2006_);
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2004_, v___x_2028_, v___x_2029_, v___x_2018_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2031_, lean_object* v_start_2032_, lean_object* v_stop_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2031_, v_start_2032_, v_stop_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec(v_stop_2033_);
lean_dec(v_start_2032_);
lean_dec_ref(v_as_2031_);
return v_res_2045_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_unsigned_to_nat(16u);
v___x_2048_ = lean_mk_array(v___x_2047_, v___x_2046_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2056_ = l_Lean_stringToMessageData(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2059_ = l_Lean_stringToMessageData(v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2277_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2277_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2277_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
uint8_t v_mbtc_2077_; 
v_mbtc_2077_ = lean_ctor_get_uint8(v_a_2073_, sizeof(void*)*14 + 18);
lean_dec(v_a_2073_);
if (v_mbtc_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec_ref(v_ctx_2060_);
v___x_2078_ = lean_box(v_mbtc_2077_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
else
{
lean_object* v___x_2082_; 
lean_del_object(v___x_2075_);
v___x_2082_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2061_, v_a_2063_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2276_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2276_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2276_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_unbox(v_a_2083_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v_toGoalState_2089_; lean_object* v_exprs_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_del_object(v___x_2085_);
v___x_2088_ = lean_st_ref_get(v_a_2061_);
v_toGoalState_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_ref(v_toGoalState_2089_);
lean_dec(v___x_2088_);
v_exprs_2090_ = lean_ctor_get(v_toGoalState_2089_, 2);
lean_inc_ref(v_exprs_2090_);
lean_dec_ref(v_toGoalState_2089_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2093_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2060_, v_exprs_2090_, v___x_2092_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec_ref(v_exprs_2090_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2262_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2262_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2262_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_snd_2098_; lean_object* v_size_2099_; lean_object* v_buckets_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2261_; 
v_snd_2098_ = lean_ctor_get(v_a_2094_, 1);
lean_inc(v_snd_2098_);
lean_dec(v_a_2094_);
v_size_2099_ = lean_ctor_get(v_snd_2098_, 0);
v_buckets_2100_ = lean_ctor_get(v_snd_2098_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_snd_2098_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2102_ = v_snd_2098_;
v_isShared_2103_ = v_isSharedCheck_2261_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_buckets_2100_);
lean_inc(v_size_2099_);
lean_dec(v_snd_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2261_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_nat_dec_eq(v_size_2099_, v___x_2091_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_del_object(v___x_2096_);
lean_dec(v_a_2083_);
v___x_2105_ = lean_st_ref_get(v_a_2061_);
v___x_2106_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___y_2109_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2165_; lean_object* v_toGoalState_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2248_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v_toGoalState_2171_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2105_, 1);
lean_dec(v_unused_2249_);
v___x_2173_ = v___x_2105_;
v_isShared_2174_ = v_isSharedCheck_2248_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_toGoalState_2171_);
lean_dec(v___x_2105_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2248_;
goto v_resetjp_2172_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_array_get_size(v___y_2109_);
v___x_2111_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2109_, v___x_2091_, v___x_2110_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec_ref(v___y_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2143_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2143_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2143_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_array_get_size(v_a_2112_);
v___x_2117_ = lean_nat_dec_eq(v___x_2116_, v___x_2091_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
lean_del_object(v___x_2114_);
v___x_2118_ = lean_box(0);
v_sz_2119_ = lean_array_size(v_a_2112_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2112_, v_sz_2119_, v___x_2120_, v___x_2118_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2112_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2121_, 0);
lean_dec(v_unused_2130_);
v___x_2123_ = v___x_2121_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2121_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = lean_box(v_mbtc_2077_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2125_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_a_2131_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2121_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2121_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_dec(v_a_2112_);
v___x_2139_ = lean_box(v___x_2104_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2139_);
v___x_2141_ = v___x_2114_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2111_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2111_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
v___jp_2152_:
{
lean_object* v___x_2157_; 
v___x_2157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2153_, v___y_2155_, v___y_2154_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec(v___y_2153_);
v___y_2109_ = v___x_2157_;
goto v___jp_2108_;
}
v___jp_2158_:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_nat_dec_le(v___y_2162_, v___y_2159_);
if (v___x_2163_ == 0)
{
lean_dec(v___y_2159_);
lean_inc(v___y_2162_);
v___y_2153_ = v___y_2160_;
v___y_2154_ = v___y_2162_;
v___y_2155_ = v___y_2161_;
v___y_2156_ = v___y_2162_;
goto v___jp_2152_;
}
else
{
v___y_2153_ = v___y_2160_;
v___y_2154_ = v___y_2162_;
v___y_2155_ = v___y_2161_;
v___y_2156_ = v___y_2159_;
goto v___jp_2152_;
}
}
v___jp_2164_:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v___y_2165_);
v___x_2167_ = lean_nat_dec_eq(v___x_2166_, v___x_2091_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_sub(v___x_2166_, v___x_2168_);
v___x_2170_ = lean_nat_dec_le(v___x_2091_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_inc(v___x_2169_);
v___y_2159_ = v___x_2169_;
v___y_2160_ = v___x_2166_;
v___y_2161_ = v___y_2165_;
v___y_2162_ = v___x_2169_;
goto v___jp_2158_;
}
else
{
v___y_2159_ = v___x_2169_;
v___y_2160_ = v___x_2166_;
v___y_2161_ = v___y_2165_;
v___y_2162_ = v___x_2091_;
goto v___jp_2158_;
}
}
else
{
v___y_2109_ = v___y_2165_;
goto v___jp_2108_;
}
}
v_resetjp_2172_:
{
lean_object* v_split_2175_; lean_object* v_splits_2176_; lean_object* v_num_2177_; uint8_t v___x_2178_; 
v_split_2175_ = lean_ctor_get(v_toGoalState_2171_, 14);
lean_inc_ref(v_split_2175_);
lean_dec_ref(v_toGoalState_2171_);
v_splits_2176_ = lean_ctor_get(v_a_2107_, 0);
lean_inc(v_splits_2176_);
lean_dec(v_a_2107_);
v_num_2177_ = lean_ctor_get(v_split_2175_, 0);
lean_inc(v_num_2177_);
lean_dec_ref(v_split_2175_);
v___x_2178_ = lean_nat_dec_lt(v_splits_2176_, v_num_2177_);
lean_dec(v_num_2177_);
lean_dec(v_splits_2176_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
lean_del_object(v___x_2173_);
lean_del_object(v___x_2102_);
v___x_2179_ = lean_mk_empty_array_with_capacity(v_size_2099_);
lean_dec(v_size_2099_);
v___x_2180_ = lean_array_get_size(v_buckets_2100_);
v___x_2181_ = lean_nat_dec_lt(v___x_2091_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v_buckets_2100_);
v___y_2165_ = v___x_2179_;
goto v___jp_2164_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_le(v___x_2180_, v___x_2180_);
if (v___x_2182_ == 0)
{
if (v___x_2181_ == 0)
{
lean_dec_ref(v_buckets_2100_);
v___y_2165_ = v___x_2179_;
goto v___jp_2164_;
}
else
{
size_t v___x_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = lean_usize_of_nat(v___x_2180_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2100_, v___x_2183_, v___x_2184_, v___x_2179_);
lean_dec_ref(v_buckets_2100_);
v___y_2165_ = v___x_2185_;
goto v___jp_2164_;
}
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2180_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2100_, v___x_2186_, v___x_2187_, v___x_2179_);
lean_dec_ref(v_buckets_2100_);
v___y_2165_ = v___x_2188_;
goto v___jp_2164_;
}
}
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_buckets_2100_);
lean_dec(v_size_2099_);
v___x_2189_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2065_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2231_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2231_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2231_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
uint8_t v_verbose_2196_; 
v_verbose_2196_ = lean_ctor_get_uint8(v_a_2192_, 0);
lean_dec(v_a_2192_);
if (v_verbose_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec(v_a_2190_);
lean_del_object(v___x_2173_);
lean_del_object(v___x_2102_);
v___x_2197_ = lean_box(v___x_2104_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2197_);
v___x_2199_ = v___x_2194_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
lean_object* v_splits_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_del_object(v___x_2194_);
v_splits_2201_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_splits_2201_);
lean_dec(v_a_2190_);
v___x_2202_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2203_ = l_Nat_reprFast(v_splits_2201_);
v___x_2204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_ofFormat(v___x_2204_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 7);
lean_ctor_set(v___x_2173_, 1, v___x_2205_);
lean_ctor_set(v___x_2173_, 0, v___x_2202_);
v___x_2207_ = v___x_2173_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2103_ == 0)
{
lean_ctor_set_tag(v___x_2102_, 7);
lean_ctor_set(v___x_2102_, 1, v___x_2208_);
lean_ctor_set(v___x_2102_, 0, v___x_2207_);
v___x_2210_ = v___x_2102_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_Meta_Sym_reportIssue(v___x_2210_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2219_; 
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v___x_2211_, 0);
lean_dec(v_unused_2220_);
v___x_2213_ = v___x_2211_;
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
else
{
lean_dec(v___x_2211_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_box(v___x_2104_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2215_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2221_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2211_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2211_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
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
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_a_2190_);
lean_del_object(v___x_2173_);
lean_del_object(v___x_2102_);
v_a_2232_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2191_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2191_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2173_);
lean_del_object(v___x_2102_);
v_a_2240_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2189_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2189_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v___x_2105_);
lean_del_object(v___x_2102_);
lean_dec_ref(v_buckets_2100_);
lean_dec(v_size_2099_);
v_a_2250_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2106_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2106_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v___x_2259_; 
lean_del_object(v___x_2102_);
lean_dec_ref(v_buckets_2100_);
lean_dec(v_size_2099_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v_a_2083_);
v___x_2259_ = v___x_2096_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2083_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2083_);
v_a_2263_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2093_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2093_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_a_2083_);
lean_dec_ref(v_ctx_2060_);
v___x_2271_ = 0;
v___x_2272_ = lean_box(v___x_2271_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2272_);
v___x_2274_ = v___x_2085_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2060_);
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_ctx_2060_);
v_a_2278_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2072_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2072_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Meta_Grind_mbtc(v_ctx_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec(v_a_2287_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2299_, lean_object* v_msg_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2299_, v_msg_2300_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2313_, lean_object* v_msg_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2313_, v_msg_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec(v___y_2315_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2327_, lean_object* v_m_2328_, lean_object* v_a_2329_, lean_object* v_b_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2328_, v_a_2329_, v_b_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2332_, lean_object* v_m_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2333_, v_a_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2336_, lean_object* v_m_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2336_, v_m_2337_, v_a_2338_);
lean_dec_ref(v_a_2338_);
lean_dec_ref(v_m_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2340_, lean_object* v_val_2341_, lean_object* v___x_2342_, lean_object* v___x_2343_, lean_object* v_as_2344_, lean_object* v_as_x27_2345_, lean_object* v_b_2346_, lean_object* v_a_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2340_, v_val_2341_, v___x_2342_, v___x_2343_, v_as_x27_2345_, v_b_2346_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2360_ = _args[0];
lean_object* v_val_2361_ = _args[1];
lean_object* v___x_2362_ = _args[2];
lean_object* v___x_2363_ = _args[3];
lean_object* v_as_2364_ = _args[4];
lean_object* v_as_x27_2365_ = _args[5];
lean_object* v_b_2366_ = _args[6];
lean_object* v_a_2367_ = _args[7];
lean_object* v___y_2368_ = _args[8];
lean_object* v___y_2369_ = _args[9];
lean_object* v___y_2370_ = _args[10];
lean_object* v___y_2371_ = _args[11];
lean_object* v___y_2372_ = _args[12];
lean_object* v___y_2373_ = _args[13];
lean_object* v___y_2374_ = _args[14];
lean_object* v___y_2375_ = _args[15];
lean_object* v___y_2376_ = _args[16];
lean_object* v___y_2377_ = _args[17];
lean_object* v___y_2378_ = _args[18];
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2360_, v_val_2361_, v___x_2362_, v___x_2363_, v_as_2364_, v_as_x27_2365_, v_b_2366_, v_a_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec(v_as_x27_2365_);
lean_dec(v_as_2364_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2380_, lean_object* v_m_2381_, lean_object* v_a_2382_, lean_object* v_b_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2381_, v_a_2382_, v_b_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2385_, lean_object* v_as_2386_, lean_object* v_lo_2387_, lean_object* v_hi_2388_, lean_object* v_w_2389_, lean_object* v_hlo_2390_, lean_object* v_hhi_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2385_, v_as_2386_, v_lo_2387_, v_hi_2388_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2393_, lean_object* v_as_2394_, lean_object* v_lo_2395_, lean_object* v_hi_2396_, lean_object* v_w_2397_, lean_object* v_hlo_2398_, lean_object* v_hhi_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2393_, v_as_2394_, v_lo_2395_, v_hi_2396_, v_w_2397_, v_hlo_2398_, v_hhi_2399_);
lean_dec(v_hi_2396_);
lean_dec(v_n_2393_);
return v_res_2400_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2401_, lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
uint8_t v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2402_, v_x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2405_, lean_object* v_a_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2405_, v_a_2406_, v_x_2407_);
lean_dec(v_x_2407_);
lean_dec_ref(v_a_2406_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2410_, lean_object* v_data_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2413_, lean_object* v_a_2414_, lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2414_, v_x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2417_, lean_object* v_a_2418_, lean_object* v_x_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2417_, v_a_2418_, v_x_2419_);
lean_dec(v_x_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2421_, lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2422_, v_x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_a_2426_, lean_object* v_x_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2425_, v_a_2426_, v_x_2427_);
lean_dec(v_x_2427_);
lean_dec_ref(v_a_2426_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2430_, lean_object* v_data_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2433_, lean_object* v_a_2434_, lean_object* v_b_2435_, lean_object* v_x_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2434_, v_b_2435_, v_x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2438_, lean_object* v_lo_2439_, lean_object* v_hi_2440_, lean_object* v_hhi_2441_, lean_object* v_pivot_2442_, lean_object* v_as_2443_, lean_object* v_i_2444_, lean_object* v_k_2445_, lean_object* v_ilo_2446_, lean_object* v_ik_2447_, lean_object* v_w_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2440_, v_pivot_2442_, v_as_2443_, v_i_2444_, v_k_2445_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2450_, lean_object* v_lo_2451_, lean_object* v_hi_2452_, lean_object* v_hhi_2453_, lean_object* v_pivot_2454_, lean_object* v_as_2455_, lean_object* v_i_2456_, lean_object* v_k_2457_, lean_object* v_ilo_2458_, lean_object* v_ik_2459_, lean_object* v_w_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2450_, v_lo_2451_, v_hi_2452_, v_hhi_2453_, v_pivot_2454_, v_as_2455_, v_i_2456_, v_k_2457_, v_ilo_2458_, v_ik_2459_, v_w_2460_);
lean_dec_ref(v_pivot_2454_);
lean_dec(v_hi_2452_);
lean_dec(v_lo_2451_);
lean_dec(v_n_2450_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2462_, lean_object* v_i_2463_, lean_object* v_source_2464_, lean_object* v_target_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2463_, v_source_2464_, v_target_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2467_, lean_object* v_i_2468_, lean_object* v_source_2469_, lean_object* v_target_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2468_, v_source_2469_, v_target_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2473_, v_x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2477_, v_x_2478_);
return v___x_2479_;
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
