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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_expr_eqv(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_4_;
v_res_4_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(v_x_1_, v_x_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(v_x_5_, v_x_6_);
lean_dec_ref(v_x_6_);
lean_dec_ref(v_x_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint64_t l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(lean_object* v_x_11_){
_start:
{
uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; 
v___x_12_ = 0ULL;
v___x_13_ = l_Lean_Expr_hash(v_x_11_);
v___x_14_ = lean_uint64_mix_hash(v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_11_ = stack[0].m_obj;
uint64_t v_res_15_;
v_res_15_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_x_11_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(lean_object* v_x_16_){
_start:
{
uint64_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_x_16_);
lean_dec_ref(v_x_16_);
v_r_18_ = lean_box_uint64(v_res_17_);
return v_r_18_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_box(0);
v___x_25_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1));
v___x_26_ = l_Lean_mkConst(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1));
v___x_33_ = l_Lean_mkConst(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark(void){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2);
return v___x_34_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(lean_object* v_upperBound_35_, lean_object* v_i_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_b_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_a_46_; uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_lt(v_a_38_, v_upperBound_35_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec(v_a_38_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v_b_39_);
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = lean_nat_dec_eq(v_i_36_, v_a_38_);
if (v___x_52_ == 0)
{
lean_object* v_paramInfo_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_paramInfo_53_ = lean_ctor_get(v_a_37_, 0);
v___x_54_ = lean_array_fget_borrowed(v_b_39_, v_a_38_);
lean_inc(v___x_54_);
v___x_55_ = l_Lean_Meta_Sym_Canon_isSupport(v_paramInfo_53_, v_a_38_, v___x_54_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; uint8_t v___x_57_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
lean_dec_ref_known(v___x_55_, 1);
v___x_57_ = lean_unbox(v_a_56_);
lean_dec(v_a_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
v___x_59_ = lean_array_fset(v_b_39_, v_a_38_, v___x_58_);
v_a_46_ = v___x_59_;
goto v___jp_45_;
}
else
{
v_a_46_ = v_b_39_;
goto v___jp_45_;
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref(v_b_39_);
lean_dec(v_a_38_);
v_a_60_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_55_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_55_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
v___x_69_ = lean_array_fset(v_b_39_, v_a_38_, v___x_68_);
v_a_46_ = v___x_69_;
goto v___jp_45_;
}
}
v___jp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_a_38_, v___x_47_);
lean_dec(v_a_38_);
v_a_38_ = v___x_48_;
v_b_39_ = v_a_46_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_35_ = stack[0].m_obj;
lean_object* v_i_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_b_39_ = stack[4].m_obj;
lean_object* v___y_40_ = stack[5].m_obj;
lean_object* v___y_41_ = stack[6].m_obj;
lean_object* v___y_42_ = stack[7].m_obj;
lean_object* v___y_43_ = stack[8].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_35_, v_i_36_, v_a_37_, v_a_38_, v_b_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(lean_object* v_upperBound_71_, lean_object* v_i_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_b_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_71_, v_i_72_, v_a_73_, v_a_74_, v_b_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec_ref(v_a_73_);
lean_dec(v_i_72_);
lean_dec(v_upperBound_71_);
return v_res_81_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(lean_object* v_i_82_, lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
if (lean_obj_tag(v_x_83_) == 5)
{
lean_object* v_fn_91_; lean_object* v_arg_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_fn_91_ = lean_ctor_get(v_x_83_, 0);
lean_inc_ref(v_fn_91_);
v_arg_92_ = lean_ctor_get(v_x_83_, 1);
lean_inc_ref(v_arg_92_);
lean_dec_ref_known(v_x_83_, 2);
v___x_93_ = lean_array_set(v_x_84_, v_x_85_, v_arg_92_);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_sub(v_x_85_, v___x_94_);
lean_dec(v_x_85_);
v_x_83_ = v_fn_91_;
v_x_84_ = v___x_93_;
v_x_85_ = v___x_95_;
goto _start;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_x_85_);
v___x_97_ = lean_box(0);
lean_inc_ref(v_x_83_);
v___x_98_ = l_Lean_Meta_getFunInfo(v_x_83_, v___x_97_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = lean_array_get_size(v_x_84_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v___x_100_, v_i_82_, v_a_99_, v___x_101_, v_x_84_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v_a_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_111_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_mkAppN(v_x_83_, v_a_103_);
lean_dec(v_a_103_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v_x_83_);
v_a_112_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_102_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_83_);
v_a_120_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_98_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_98_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_82_ = stack[0].m_obj;
lean_object* v_x_83_ = stack[1].m_obj;
lean_object* v_x_84_ = stack[2].m_obj;
lean_object* v_x_85_ = stack[3].m_obj;
lean_object* v___y_86_ = stack[4].m_obj;
lean_object* v___y_87_ = stack[5].m_obj;
lean_object* v___y_88_ = stack[6].m_obj;
lean_object* v___y_89_ = stack[7].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_82_, v_x_83_, v_x_84_, v_x_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(lean_object* v_i_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_129_, v_x_130_, v_x_131_, v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v_i_129_);
return v_res_138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v_dummy_140_; 
v___x_139_ = lean_box(0);
v_dummy_140_ = l_Lean_Expr_sort___override(v___x_139_);
return v_dummy_140_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(lean_object* v_e_141_, lean_object* v_i_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_dummy_148_; lean_object* v_nargs_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_dummy_148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_149_ = l_Lean_Expr_getAppNumArgs(v_e_141_);
lean_inc(v_nargs_149_);
v___x_150_ = lean_mk_array(v_nargs_149_, v_dummy_148_);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_sub(v_nargs_149_, v___x_151_);
lean_dec(v_nargs_149_);
v___x_153_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_142_, v_e_141_, v___x_150_, v___x_152_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_153_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_141_ = stack[0].m_obj;
lean_object* v_i_142_ = stack[1].m_obj;
lean_object* v_a_143_ = stack[2].m_obj;
lean_object* v_a_144_ = stack[3].m_obj;
lean_object* v_a_145_ = stack[4].m_obj;
lean_object* v_a_146_ = stack[5].m_obj;
lean_object* v_res_154_;
v_res_154_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_141_, v_i_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(lean_object* v_e_155_, lean_object* v_i_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_155_, v_i_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_i_156_);
return v_res_162_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(lean_object* v_upperBound_163_, lean_object* v_i_164_, lean_object* v_a_165_, lean_object* v___x_166_, lean_object* v_inst_167_, lean_object* v_R_168_, lean_object* v_a_169_, lean_object* v_b_170_, lean_object* v_c_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_163_, v_i_164_, v_a_165_, v_a_169_, v_b_170_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
return v___x_177_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_163_ = stack[0].m_obj;
lean_object* v_i_164_ = stack[1].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
lean_object* v___x_166_ = stack[3].m_obj;
lean_object* v_a_169_ = stack[6].m_obj;
lean_object* v_b_170_ = stack[7].m_obj;
lean_object* v___y_172_ = stack[9].m_obj;
lean_object* v___y_173_ = stack[10].m_obj;
lean_object* v___y_174_ = stack[11].m_obj;
lean_object* v___y_175_ = stack[12].m_obj;
lean_object* v_res_178_;
v_res_178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_163_, v_i_164_, v_a_165_, v___x_166_, lean_box(0), lean_box(0), v_a_169_, v_b_170_, lean_box(0), v___y_172_, v___y_173_, v___y_174_, v___y_175_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(lean_object* v_upperBound_179_, lean_object* v_i_180_, lean_object* v_a_181_, lean_object* v___x_182_, lean_object* v_inst_183_, lean_object* v_R_184_, lean_object* v_a_185_, lean_object* v_b_186_, lean_object* v_c_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_179_, v_i_180_, v_a_181_, v___x_182_, v_inst_183_, v_R_184_, v_a_185_, v_b_186_, v_c_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___x_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_i_180_);
lean_dec(v_upperBound_179_);
return v_res_193_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(lean_object* v_a_194_, lean_object* v_b_195_, lean_object* v_i_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_arg_204_; lean_object* v_app_205_; lean_object* v_arg_206_; lean_object* v_app_207_; lean_object* v_fst_209_; lean_object* v_snd_210_; uint8_t v___x_250_; 
v_arg_204_ = lean_ctor_get(v_a_194_, 0);
lean_inc_ref(v_arg_204_);
v_app_205_ = lean_ctor_get(v_a_194_, 1);
lean_inc_ref(v_app_205_);
lean_dec_ref(v_a_194_);
v_arg_206_ = lean_ctor_get(v_b_195_, 0);
lean_inc_ref(v_arg_206_);
v_app_207_ = lean_ctor_get(v_b_195_, 1);
lean_inc_ref(v_app_207_);
lean_dec_ref(v_b_195_);
v___x_250_ = lean_expr_lt(v_arg_204_, v_arg_206_);
if (v___x_250_ == 0)
{
v_fst_209_ = v_arg_206_;
v_snd_210_ = v_arg_204_;
goto v___jp_208_;
}
else
{
v_fst_209_ = v_arg_204_;
v_snd_210_ = v_arg_206_;
goto v___jp_208_;
}
v___jp_208_:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_mkEq(v_fst_209_, v_snd_210_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_Lean_Meta_Sym_canon(v_a_212_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_Meta_Sym_shareCommon(v_a_214_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_225_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_225_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
lean_inc(v_i_196_);
lean_inc_ref(v_app_207_);
lean_inc_ref(v_app_205_);
v___x_220_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_220_, 0, v_app_205_);
lean_ctor_set(v___x_220_, 1, v_app_207_);
lean_ctor_set(v___x_220_, 2, v_i_196_);
v___x_221_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_221_, 0, v_app_205_);
lean_ctor_set(v___x_221_, 1, v_app_207_);
lean_ctor_set(v___x_221_, 2, v_i_196_);
lean_ctor_set(v___x_221_, 3, v_a_216_);
lean_ctor_set(v___x_221_, 4, v___x_220_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_app_207_);
lean_dec_ref(v_app_205_);
lean_dec(v_i_196_);
v_a_226_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_215_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_215_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_app_207_);
lean_dec_ref(v_app_205_);
lean_dec(v_i_196_);
v_a_234_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_213_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_213_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_app_207_);
lean_dec_ref(v_app_205_);
lean_dec(v_i_196_);
v_a_242_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_211_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_211_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_194_ = stack[0].m_obj;
lean_object* v_b_195_ = stack[1].m_obj;
lean_object* v_i_196_ = stack[2].m_obj;
lean_object* v_a_197_ = stack[3].m_obj;
lean_object* v_a_198_ = stack[4].m_obj;
lean_object* v_a_199_ = stack[5].m_obj;
lean_object* v_a_200_ = stack[6].m_obj;
lean_object* v_a_201_ = stack[7].m_obj;
lean_object* v_a_202_ = stack[8].m_obj;
lean_object* v_res_251_;
v_res_251_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_194_, v_b_195_, v_i_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg___boxed(lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_i_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_252_, v_b_253_, v_i_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_262_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(lean_object* v_a_263_, lean_object* v_b_264_, lean_object* v_i_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v_a_263_, v_b_264_, v_i_265_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
return v___x_277_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_263_ = stack[0].m_obj;
lean_object* v_b_264_ = stack[1].m_obj;
lean_object* v_i_265_ = stack[2].m_obj;
lean_object* v_a_266_ = stack[3].m_obj;
lean_object* v_a_267_ = stack[4].m_obj;
lean_object* v_a_268_ = stack[5].m_obj;
lean_object* v_a_269_ = stack[6].m_obj;
lean_object* v_a_270_ = stack[7].m_obj;
lean_object* v_a_271_ = stack[8].m_obj;
lean_object* v_a_272_ = stack[9].m_obj;
lean_object* v_a_273_ = stack[10].m_obj;
lean_object* v_a_274_ = stack[11].m_obj;
lean_object* v_a_275_ = stack[12].m_obj;
lean_object* v_res_278_;
v_res_278_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(v_a_263_, v_b_264_, v_i_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(lean_object* v_a_279_, lean_object* v_b_280_, lean_object* v_i_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(v_a_279_, v_b_280_, v_i_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec(v_a_282_);
return v_res_293_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(lean_object* v_declName_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_env_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_297_);
v___x_299_ = l_Lean_isInstanceReducibleCore(v_env_298_, v_declName_294_);
v___x_300_ = lean_box(v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_294_ = stack[0].m_obj;
lean_object* v___y_295_ = stack[1].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_294_, v___y_295_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(lean_object* v_declName_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_303_, v___y_304_);
lean_dec(v___y_304_);
return v_res_306_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(lean_object* v_declName_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_307_, v___y_309_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_307_ = stack[0].m_obj;
lean_object* v___y_308_ = stack[1].m_obj;
lean_object* v___y_309_ = stack[2].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(lean_object* v_declName_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(lean_object* v_f_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
if (lean_obj_tag(v_f_318_) == 4)
{
lean_object* v_declName_322_; lean_object* v___x_323_; 
v_declName_322_ = lean_ctor_get(v_f_318_, 0);
lean_inc(v_declName_322_);
lean_dec_ref_known(v_f_318_, 2);
v___x_323_ = l_Lean_isInstanceReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_322_, v_a_320_);
return v___x_323_;
}
else
{
uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v_f_318_);
v___x_324_ = 0;
v___x_325_ = lean_box(v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_318_ = stack[0].m_obj;
lean_object* v_a_319_ = stack[1].m_obj;
lean_object* v_a_320_ = stack[2].m_obj;
lean_object* v_res_327_;
v_res_327_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v_f_318_, v_a_319_, v_a_320_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(lean_object* v_f_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v_f_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
return v_res_332_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* v_as_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_lt(v_i_335_, v_sz_334_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_b_336_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
v_a_351_ = lean_array_uget_borrowed(v_as_333_, v_i_335_);
lean_inc(v_a_351_);
v___x_352_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_351_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_352_) == 0)
{
size_t v___x_353_; size_t v___x_354_; 
lean_dec_ref_known(v___x_352_, 1);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_335_, v___x_353_);
v_i_335_ = v___x_354_;
v_b_336_ = v___x_350_;
goto _start;
}
else
{
return v___x_352_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_333_ = stack[0].m_obj;
size_t v_sz_334_ = stack[1].m_num;
size_t v_i_335_ = stack[2].m_num;
lean_object* v_b_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v___y_338_ = stack[5].m_obj;
lean_object* v___y_339_ = stack[6].m_obj;
lean_object* v___y_340_ = stack[7].m_obj;
lean_object* v___y_341_ = stack[8].m_obj;
lean_object* v___y_342_ = stack[9].m_obj;
lean_object* v___y_343_ = stack[10].m_obj;
lean_object* v___y_344_ = stack[11].m_obj;
lean_object* v___y_345_ = stack[12].m_obj;
lean_object* v___y_346_ = stack[13].m_obj;
lean_object* v_res_356_;
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_333_, v_sz_334_, v_i_335_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* v_as_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
size_t v_sz_boxed_372_; size_t v_i_boxed_373_; lean_object* v_res_374_; 
v_sz_boxed_372_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_373_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_357_, v_sz_boxed_372_, v_i_boxed_373_, v_b_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v_as_357_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
return v_x_375_;
}
else
{
lean_object* v_key_377_; lean_object* v_tail_378_; lean_object* v___x_379_; 
v_key_377_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_key_377_);
v_tail_378_ = lean_ctor_get(v_x_376_, 2);
lean_inc(v_tail_378_);
lean_dec_ref_known(v_x_376_, 3);
v___x_379_ = lean_array_push(v_x_375_, v_key_377_);
v_x_375_ = v___x_379_;
v_x_376_ = v_tail_378_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object* v_as_381_, size_t v_i_382_, size_t v_stop_383_, lean_object* v_b_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_eq(v_i_382_, v_stop_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; size_t v___x_388_; size_t v___x_389_; 
v___x_386_ = lean_array_uget_borrowed(v_as_381_, v_i_382_);
lean_inc(v___x_386_);
v___x_387_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(v_b_384_, v___x_386_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_382_, v___x_388_);
v_i_382_ = v___x_389_;
v_b_384_ = v___x_387_;
goto _start;
}
else
{
return v_b_384_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_381_ = stack[0].m_obj;
size_t v_i_382_ = stack[1].m_num;
size_t v_stop_383_ = stack[2].m_num;
lean_object* v_b_384_ = stack[3].m_obj;
lean_object* v_res_391_;
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_381_, v_i_382_, v_stop_383_, v_b_384_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object* v_as_392_, lean_object* v_i_393_, lean_object* v_stop_394_, lean_object* v_b_395_){
_start:
{
size_t v_i_boxed_396_; size_t v_stop_boxed_397_; lean_object* v_res_398_; 
v_i_boxed_396_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_394_);
lean_dec(v_stop_394_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_392_, v_i_boxed_396_, v_stop_boxed_397_, v_b_395_);
lean_dec_ref(v_as_392_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(lean_object* v_hi_399_, lean_object* v_pivot_400_, lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_k_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_lt(v_k_403_, v_hi_399_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_k_403_);
v___x_405_ = lean_array_fswap(v_as_401_, v_i_402_, v_hi_399_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_i_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_array_fget_borrowed(v_as_401_, v_k_403_);
v___x_408_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_407_, v_pivot_400_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_k_403_, v___x_409_);
lean_dec(v_k_403_);
v_k_403_ = v___x_410_;
goto _start;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_array_fswap(v_as_401_, v_i_402_, v_k_403_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_i_402_, v___x_413_);
lean_dec(v_i_402_);
v___x_415_ = lean_nat_add(v_k_403_, v___x_413_);
lean_dec(v_k_403_);
v_as_401_ = v___x_412_;
v_i_402_ = v___x_414_;
v_k_403_ = v___x_415_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg___boxed(lean_object* v_hi_417_, lean_object* v_pivot_418_, lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_k_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_417_, v_pivot_418_, v_as_419_, v_i_420_, v_k_421_);
lean_dec_ref(v_pivot_418_);
lean_dec(v_hi_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(lean_object* v_n_423_, lean_object* v_as_424_, lean_object* v_lo_425_, lean_object* v_hi_426_){
_start:
{
lean_object* v___y_428_; uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_lt(v_lo_425_, v_hi_426_);
if (v___x_438_ == 0)
{
lean_dec(v_lo_425_);
return v_as_424_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_mid_441_; lean_object* v___y_443_; lean_object* v___y_449_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_439_ = lean_nat_add(v_lo_425_, v_hi_426_);
v___x_440_ = lean_unsigned_to_nat(1u);
v_mid_441_ = lean_nat_shiftr(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
v___x_454_ = lean_array_fget_borrowed(v_as_424_, v_mid_441_);
v___x_455_ = lean_array_fget_borrowed(v_as_424_, v_lo_425_);
v___x_456_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
v___y_449_ = v_as_424_;
goto v___jp_448_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_array_fswap(v_as_424_, v_lo_425_, v_mid_441_);
v___y_449_ = v___x_457_;
goto v___jp_448_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_array_fget_borrowed(v___y_443_, v_mid_441_);
v___x_445_ = lean_array_fget_borrowed(v___y_443_, v_hi_426_);
v___x_446_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_dec(v_mid_441_);
v___y_428_ = v___y_443_;
goto v___jp_427_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_array_fswap(v___y_443_, v_mid_441_, v_hi_426_);
lean_dec(v_mid_441_);
v___y_428_ = v___x_447_;
goto v___jp_427_;
}
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_array_fget_borrowed(v___y_449_, v_hi_426_);
v___x_451_ = lean_array_fget_borrowed(v___y_449_, v_lo_425_);
v___x_452_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_443_ = v___y_449_;
goto v___jp_442_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_array_fswap(v___y_449_, v_lo_425_, v_hi_426_);
v___y_443_ = v___x_453_;
goto v___jp_442_;
}
}
}
v___jp_427_:
{
lean_object* v_pivot_429_; lean_object* v___x_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; uint8_t v___x_433_; 
v_pivot_429_ = lean_array_fget(v___y_428_, v_hi_426_);
lean_inc_n(v_lo_425_, 2);
v___x_430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_426_, v_pivot_429_, v___y_428_, v_lo_425_, v_lo_425_);
lean_dec(v_pivot_429_);
v_fst_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_snd_432_);
lean_dec_ref(v___x_430_);
v___x_433_ = lean_nat_dec_le(v_hi_426_, v_fst_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_423_, v_snd_432_, v_lo_425_, v_fst_431_);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_add(v_fst_431_, v___x_435_);
lean_dec(v_fst_431_);
v_as_424_ = v___x_434_;
v_lo_425_ = v___x_436_;
goto _start;
}
else
{
lean_dec(v_fst_431_);
lean_dec(v_lo_425_);
return v_snd_432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(lean_object* v_n_458_, lean_object* v_as_459_, lean_object* v_lo_460_, lean_object* v_hi_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_458_, v_as_459_, v_lo_460_, v_hi_461_);
lean_dec(v_hi_461_);
lean_dec(v_n_458_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_key_466_; lean_object* v_value_467_; lean_object* v_tail_468_; uint8_t v___x_469_; 
v_key_466_ = lean_ctor_get(v_x_464_, 0);
v_value_467_ = lean_ctor_get(v_x_464_, 1);
v_tail_468_ = lean_ctor_get(v_x_464_, 2);
v___x_469_ = lean_expr_eqv(v_key_466_, v_a_463_);
if (v___x_469_ == 0)
{
v_x_464_ = v_tail_468_;
goto _start;
}
else
{
lean_object* v___x_471_; 
lean_inc(v_value_467_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_value_467_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object* v_a_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_472_, v_x_473_);
lean_dec(v_x_473_);
lean_dec_ref(v_a_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_buckets_477_; lean_object* v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v_fold_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_buckets_477_ = lean_ctor_get(v_m_475_, 1);
v___x_478_ = lean_array_get_size(v_buckets_477_);
v___x_479_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_476_);
v___x_480_ = 32ULL;
v___x_481_ = lean_uint64_shift_right(v___x_479_, v___x_480_);
v_fold_482_ = lean_uint64_xor(v___x_479_, v___x_481_);
v___x_483_ = 16ULL;
v___x_484_ = lean_uint64_shift_right(v_fold_482_, v___x_483_);
v___x_485_ = lean_uint64_xor(v_fold_482_, v___x_484_);
v___x_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = lean_usize_of_nat(v___x_478_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_sub(v___x_487_, v___x_488_);
v___x_490_ = lean_usize_land(v___x_486_, v___x_489_);
v___x_491_ = lean_array_uget_borrowed(v_buckets_477_, v___x_490_);
v___x_492_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_476_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object* v_m_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_493_, v_a_494_);
lean_dec_ref(v_a_494_);
lean_dec_ref(v_m_493_);
return v_res_495_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object* v_msgData_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; lean_object* v_env_503_; uint8_t v___x_504_; lean_object* v_env_505_; lean_object* v___x_506_; lean_object* v_toCold_507_; lean_object* v_mctx_508_; lean_object* v_lctx_509_; lean_object* v_options_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_502_ = lean_st_ref_get(v___y_500_);
v_env_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc_ref(v_env_503_);
lean_dec(v___x_502_);
v___x_504_ = 0;
v_env_505_ = l_Lean_Environment_setRecordingDeps(v_env_503_, v___x_504_);
v___x_506_ = lean_st_ref_get(v___y_498_);
v_toCold_507_ = lean_ctor_get(v___y_499_, 0);
v_mctx_508_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_mctx_508_);
lean_dec(v___x_506_);
v_lctx_509_ = lean_ctor_get(v___y_497_, 2);
v_options_510_ = lean_ctor_get(v_toCold_507_, 2);
lean_inc_ref(v_options_510_);
lean_inc_ref(v_lctx_509_);
v___x_511_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_511_, 0, v_env_505_);
lean_ctor_set(v___x_511_, 1, v_mctx_508_);
lean_ctor_set(v___x_511_, 2, v_lctx_509_);
lean_ctor_set(v___x_511_, 3, v_options_510_);
v___x_512_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_msgData_496_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_496_ = stack[0].m_obj;
lean_object* v___y_497_ = stack[1].m_obj;
lean_object* v___y_498_ = stack[2].m_obj;
lean_object* v___y_499_ = stack[3].m_obj;
lean_object* v___y_500_ = stack[4].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object* v_msgData_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_521_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_522_; double v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_float_of_nat(v___x_522_);
return v___x_523_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* v_cls_527_, lean_object* v_msg_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_ref_534_; lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_581_; 
v_ref_534_ = lean_ctor_get(v___y_531_, 2);
v___x_535_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_581_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_581_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_581_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v_traceState_541_; lean_object* v_env_542_; lean_object* v_nextMacroScope_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_cache_546_; lean_object* v_recordedDeps_547_; lean_object* v_messages_548_; lean_object* v_infoState_549_; lean_object* v_snapshotTasks_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_580_; 
v___x_540_ = lean_st_ref_take(v___y_532_);
v_traceState_541_ = lean_ctor_get(v___x_540_, 4);
v_env_542_ = lean_ctor_get(v___x_540_, 0);
v_nextMacroScope_543_ = lean_ctor_get(v___x_540_, 1);
v_ngen_544_ = lean_ctor_get(v___x_540_, 2);
v_auxDeclNGen_545_ = lean_ctor_get(v___x_540_, 3);
v_cache_546_ = lean_ctor_get(v___x_540_, 5);
v_recordedDeps_547_ = lean_ctor_get(v___x_540_, 6);
v_messages_548_ = lean_ctor_get(v___x_540_, 7);
v_infoState_549_ = lean_ctor_get(v___x_540_, 8);
v_snapshotTasks_550_ = lean_ctor_get(v___x_540_, 9);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_580_ == 0)
{
v___x_552_ = v___x_540_;
v_isShared_553_ = v_isSharedCheck_580_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snapshotTasks_550_);
lean_inc(v_infoState_549_);
lean_inc(v_messages_548_);
lean_inc(v_recordedDeps_547_);
lean_inc(v_cache_546_);
lean_inc(v_traceState_541_);
lean_inc(v_auxDeclNGen_545_);
lean_inc(v_ngen_544_);
lean_inc(v_nextMacroScope_543_);
lean_inc(v_env_542_);
lean_dec(v___x_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_580_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint64_t v_tid_554_; lean_object* v_traces_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_579_; 
v_tid_554_ = lean_ctor_get_uint64(v_traceState_541_, sizeof(void*)*1);
v_traces_555_ = lean_ctor_get(v_traceState_541_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_traceState_541_);
if (v_isSharedCheck_579_ == 0)
{
v___x_557_ = v_traceState_541_;
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_traces_555_);
lean_dec(v_traceState_541_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; double v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_box(0);
v___x_561_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_562_ = 0;
v___x_563_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_564_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_564_, 0, v_cls_527_);
lean_ctor_set(v___x_564_, 1, v___x_560_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
lean_ctor_set_float(v___x_564_, sizeof(void*)*3, v___x_561_);
lean_ctor_set_float(v___x_564_, sizeof(void*)*3 + 8, v___x_561_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3 + 16, v___x_562_);
v___x_565_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_566_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v_a_536_);
lean_ctor_set(v___x_566_, 2, v___x_565_);
lean_inc(v_ref_534_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_ref_534_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_PersistentArray_push___redArg(v_traces_555_, v___x_567_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_568_);
v___x_570_ = v___x_557_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_568_);
lean_ctor_set_uint64(v_reuseFailAlloc_578_, sizeof(void*)*1, v_tid_554_);
v___x_570_ = v_reuseFailAlloc_578_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 4, v___x_570_);
v___x_572_ = v___x_552_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_env_542_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_nextMacroScope_543_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_ngen_544_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_auxDeclNGen_545_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 5, v_cache_546_);
lean_ctor_set(v_reuseFailAlloc_577_, 6, v_recordedDeps_547_);
lean_ctor_set(v_reuseFailAlloc_577_, 7, v_messages_548_);
lean_ctor_set(v_reuseFailAlloc_577_, 8, v_infoState_549_);
lean_ctor_set(v_reuseFailAlloc_577_, 9, v_snapshotTasks_550_);
v___x_572_ = v_reuseFailAlloc_577_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = lean_st_ref_put(v___y_532_, v___x_572_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_559_);
v___x_575_ = v___x_538_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_559_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_527_ = stack[0].m_obj;
lean_object* v_msg_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v___y_532_ = stack[5].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_527_, v_msg_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_583_, lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_583_, v_msg_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_590_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_a_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
else
{
lean_object* v_key_594_; lean_object* v_tail_595_; uint8_t v___x_596_; 
v_key_594_ = lean_ctor_get(v_x_592_, 0);
v_tail_595_ = lean_ctor_get(v_x_592_, 2);
v___x_596_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_594_, v_a_591_);
if (v___x_596_ == 0)
{
v_x_592_ = v_tail_595_;
goto _start;
}
else
{
return v___x_596_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_591_ = stack[0].m_obj;
lean_object* v_x_592_ = stack[1].m_obj;
uint8_t v_res_598_;
v_res_598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_591_, v_x_592_);
stack->m_num = v_res_598_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_a_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec_ref(v_a_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
return v_x_603_;
}
else
{
lean_object* v_key_605_; lean_object* v_value_606_; lean_object* v_tail_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_630_; 
v_key_605_ = lean_ctor_get(v_x_604_, 0);
v_value_606_ = lean_ctor_get(v_x_604_, 1);
v_tail_607_ = lean_ctor_get(v_x_604_, 2);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_630_ == 0)
{
v___x_609_ = v_x_604_;
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_tail_607_);
lean_inc(v_value_606_);
lean_inc(v_key_605_);
lean_dec(v_x_604_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; uint64_t v___x_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v_fold_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_611_ = lean_array_get_size(v_x_603_);
v___x_612_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_605_);
v___x_613_ = 32ULL;
v___x_614_ = lean_uint64_shift_right(v___x_612_, v___x_613_);
v_fold_615_ = lean_uint64_xor(v___x_612_, v___x_614_);
v___x_616_ = 16ULL;
v___x_617_ = lean_uint64_shift_right(v_fold_615_, v___x_616_);
v___x_618_ = lean_uint64_xor(v_fold_615_, v___x_617_);
v___x_619_ = lean_uint64_to_usize(v___x_618_);
v___x_620_ = lean_usize_of_nat(v___x_611_);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_sub(v___x_620_, v___x_621_);
v___x_623_ = lean_usize_land(v___x_619_, v___x_622_);
v___x_624_ = lean_array_uget_borrowed(v_x_603_, v___x_623_);
lean_inc(v___x_624_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 2, v___x_624_);
v___x_626_ = v___x_609_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_key_605_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_value_606_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v___x_624_);
v___x_626_ = v_reuseFailAlloc_629_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_array_uset(v_x_603_, v___x_623_, v___x_626_);
v_x_603_ = v___x_627_;
v_x_604_ = v_tail_607_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object* v_i_631_, lean_object* v_source_632_, lean_object* v_target_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_source_632_);
v___x_635_ = lean_nat_dec_lt(v_i_631_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_source_632_);
lean_dec(v_i_631_);
return v_target_633_;
}
else
{
lean_object* v_es_636_; lean_object* v___x_637_; lean_object* v_source_638_; lean_object* v_target_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_es_636_ = lean_array_fget(v_source_632_, v_i_631_);
v___x_637_ = lean_box(0);
v_source_638_ = lean_array_fset(v_source_632_, v_i_631_, v___x_637_);
v_target_639_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_633_, v_es_636_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_i_631_, v___x_640_);
lean_dec(v_i_631_);
v_i_631_ = v___x_641_;
v_source_632_ = v_source_638_;
v_target_633_ = v_target_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object* v_data_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_nbuckets_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_644_ = lean_array_get_size(v_data_643_);
v___x_645_ = lean_unsigned_to_nat(2u);
v_nbuckets_646_ = lean_nat_mul(v___x_644_, v___x_645_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_box(0);
v___x_649_ = lean_mk_array(v_nbuckets_646_, v___x_648_);
v___x_650_ = lean_array_propagate_mark(v_data_643_, v___x_649_);
v___x_651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_647_, v_data_643_, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_652_, lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
lean_object* v_size_655_; lean_object* v_buckets_656_; lean_object* v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v_fold_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v_bkt_670_; uint8_t v___x_671_; 
v_size_655_ = lean_ctor_get(v_m_652_, 0);
v_buckets_656_ = lean_ctor_get(v_m_652_, 1);
v___x_657_ = lean_array_get_size(v_buckets_656_);
v___x_658_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_653_);
v___x_659_ = 32ULL;
v___x_660_ = lean_uint64_shift_right(v___x_658_, v___x_659_);
v_fold_661_ = lean_uint64_xor(v___x_658_, v___x_660_);
v___x_662_ = 16ULL;
v___x_663_ = lean_uint64_shift_right(v_fold_661_, v___x_662_);
v___x_664_ = lean_uint64_xor(v_fold_661_, v___x_663_);
v___x_665_ = lean_uint64_to_usize(v___x_664_);
v___x_666_ = lean_usize_of_nat(v___x_657_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_sub(v___x_666_, v___x_667_);
v___x_669_ = lean_usize_land(v___x_665_, v___x_668_);
v_bkt_670_ = lean_array_uget_borrowed(v_buckets_656_, v___x_669_);
v___x_671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_653_, v_bkt_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_692_; 
lean_inc_ref(v_buckets_656_);
lean_inc(v_size_655_);
v_isSharedCheck_692_ = !lean_is_exclusive(v_m_652_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_693_ = lean_ctor_get(v_m_652_, 1);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_m_652_, 0);
lean_dec(v_unused_694_);
v___x_673_ = v_m_652_;
v_isShared_674_ = v_isSharedCheck_692_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_m_652_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_692_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v_size_x27_676_; lean_object* v___x_677_; lean_object* v_buckets_x27_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v_size_x27_676_ = lean_nat_add(v_size_655_, v___x_675_);
lean_dec(v_size_655_);
lean_inc(v_bkt_670_);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v_a_653_);
lean_ctor_set(v___x_677_, 1, v_b_654_);
lean_ctor_set(v___x_677_, 2, v_bkt_670_);
v_buckets_x27_678_ = lean_array_uset(v_buckets_656_, v___x_669_, v___x_677_);
v___x_679_ = lean_unsigned_to_nat(4u);
v___x_680_ = lean_nat_mul(v_size_x27_676_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(3u);
v___x_682_ = lean_nat_div(v___x_680_, v___x_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_array_get_size(v_buckets_x27_678_);
v___x_684_ = lean_nat_dec_le(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
if (v___x_684_ == 0)
{
lean_object* v_val_685_; lean_object* v___x_687_; 
v_val_685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_678_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_val_685_);
lean_ctor_set(v___x_673_, 0, v_size_x27_676_);
v___x_687_ = v___x_673_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_size_x27_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_val_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_690_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_buckets_x27_678_);
lean_ctor_set(v___x_673_, 0, v_size_x27_676_);
v___x_690_ = v___x_673_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_size_x27_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_buckets_x27_678_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_dec(v_b_654_);
lean_dec_ref(v_a_653_);
return v_m_652_;
}
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_ctx_695_, lean_object* v_val_696_, lean_object* v___x_697_, lean_object* v___x_698_, lean_object* v_as_x27_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
if (lean_obj_tag(v_as_x27_699_) == 0)
{
lean_object* v___x_712_; 
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v_val_696_);
lean_dec_ref(v_ctx_695_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_b_700_);
return v___x_712_;
}
else
{
lean_object* v_head_713_; lean_object* v_tail_714_; lean_object* v_eqAssignment_715_; lean_object* v_arg_716_; lean_object* v___x_717_; 
v_head_713_ = lean_ctor_get(v_as_x27_699_, 0);
v_tail_714_ = lean_ctor_get(v_as_x27_699_, 1);
v_eqAssignment_715_ = lean_ctor_get(v_ctx_695_, 2);
v_arg_716_ = lean_ctor_get(v_head_713_, 0);
lean_inc_ref(v_eqAssignment_715_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v_arg_716_);
lean_inc_ref(v_val_696_);
v___x_717_ = lean_apply_13(v_eqAssignment_715_, v_val_696_, v_arg_716_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, lean_box(0));
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; uint8_t v___x_719_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
if (v___x_719_ == 0)
{
v_as_x27_699_ = v_tail_714_;
goto _start;
}
else
{
lean_object* v___x_721_; 
lean_inc_ref(v_arg_716_);
lean_inc_ref(v_val_696_);
v___x_721_ = l_Lean_Meta_Grind_hasSameType(v_val_696_, v_arg_716_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; uint8_t v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_723_ == 0)
{
v_as_x27_699_ = v_tail_714_;
goto _start;
}
else
{
lean_object* v___x_725_; 
lean_inc(v___x_698_);
lean_inc(v_head_713_);
lean_inc_ref(v___x_697_);
v___x_725_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_697_, v_head_713_, v___x_698_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_box(0);
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_700_, v_a_726_, v___x_727_);
v_as_x27_699_ = v_tail_714_;
v_b_700_ = v___x_728_;
goto _start;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_b_700_);
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v_val_696_);
lean_dec_ref(v_ctx_695_);
v_a_730_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_725_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_725_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_b_700_);
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v_val_696_);
lean_dec_ref(v_ctx_695_);
v_a_738_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_721_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_721_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_b_700_);
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v_val_696_);
lean_dec_ref(v_ctx_695_);
v_a_746_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_717_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_717_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_695_ = stack[0].m_obj;
lean_object* v_val_696_ = stack[1].m_obj;
lean_object* v___x_697_ = stack[2].m_obj;
lean_object* v___x_698_ = stack[3].m_obj;
lean_object* v_as_x27_699_ = stack[4].m_obj;
lean_object* v_b_700_ = stack[5].m_obj;
lean_object* v___y_701_ = stack[6].m_obj;
lean_object* v___y_702_ = stack[7].m_obj;
lean_object* v___y_703_ = stack[8].m_obj;
lean_object* v___y_704_ = stack[9].m_obj;
lean_object* v___y_705_ = stack[10].m_obj;
lean_object* v___y_706_ = stack[11].m_obj;
lean_object* v___y_707_ = stack[12].m_obj;
lean_object* v___y_708_ = stack[13].m_obj;
lean_object* v___y_709_ = stack[14].m_obj;
lean_object* v___y_710_ = stack[15].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_695_, v_val_696_, v___x_697_, v___x_698_, v_as_x27_699_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_ctx_755_ = _args[0];
lean_object* v_val_756_ = _args[1];
lean_object* v___x_757_ = _args[2];
lean_object* v___x_758_ = _args[3];
lean_object* v_as_x27_759_ = _args[4];
lean_object* v_b_760_ = _args[5];
lean_object* v___y_761_ = _args[6];
lean_object* v___y_762_ = _args[7];
lean_object* v___y_763_ = _args[8];
lean_object* v___y_764_ = _args[9];
lean_object* v___y_765_ = _args[10];
lean_object* v___y_766_ = _args[11];
lean_object* v___y_767_ = _args[12];
lean_object* v___y_768_ = _args[13];
lean_object* v___y_769_ = _args[14];
lean_object* v___y_770_ = _args[15];
lean_object* v___y_771_ = _args[16];
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_755_, v_val_756_, v___x_757_, v___x_758_, v_as_x27_759_, v_b_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v_as_x27_759_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* v_a_773_, lean_object* v_b_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
lean_dec(v_b_774_);
lean_dec_ref(v_a_773_);
return v_x_775_;
}
else
{
lean_object* v_key_776_; lean_object* v_value_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_790_; 
v_key_776_ = lean_ctor_get(v_x_775_, 0);
v_value_777_ = lean_ctor_get(v_x_775_, 1);
v_tail_778_ = lean_ctor_get(v_x_775_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_790_ == 0)
{
v___x_780_ = v_x_775_;
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_value_777_);
lean_inc(v_key_776_);
lean_dec(v_x_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
uint8_t v___x_782_; 
v___x_782_ = lean_expr_eqv(v_key_776_, v_a_773_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_773_, v_b_774_, v_tail_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 2, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_key_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_value_777_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_value_777_);
lean_dec(v_key_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v_b_774_);
lean_ctor_set(v___x_780_, 0, v_a_773_);
v___x_788_ = v___x_780_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_773_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_b_774_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_tail_778_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
else
{
lean_object* v_key_794_; lean_object* v_tail_795_; uint8_t v___x_796_; 
v_key_794_ = lean_ctor_get(v_x_792_, 0);
v_tail_795_ = lean_ctor_get(v_x_792_, 2);
v___x_796_ = lean_expr_eqv(v_key_794_, v_a_791_);
if (v___x_796_ == 0)
{
v_x_792_ = v_tail_795_;
goto _start;
}
else
{
return v___x_796_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_791_ = stack[0].m_obj;
lean_object* v_x_792_ = stack[1].m_obj;
uint8_t v_res_798_;
v_res_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_791_, v_x_792_);
stack->m_num = v_res_798_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_799_, v_x_800_);
lean_dec(v_x_800_);
lean_dec_ref(v_a_799_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
return v_x_803_;
}
else
{
lean_object* v_key_805_; lean_object* v_value_806_; lean_object* v_tail_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_830_; 
v_key_805_ = lean_ctor_get(v_x_804_, 0);
v_value_806_ = lean_ctor_get(v_x_804_, 1);
v_tail_807_ = lean_ctor_get(v_x_804_, 2);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_830_ == 0)
{
v___x_809_ = v_x_804_;
v_isShared_810_ = v_isSharedCheck_830_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_tail_807_);
lean_inc(v_value_806_);
lean_inc(v_key_805_);
lean_dec(v_x_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_830_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v_fold_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_811_ = lean_array_get_size(v_x_803_);
v___x_812_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_805_);
v___x_813_ = 32ULL;
v___x_814_ = lean_uint64_shift_right(v___x_812_, v___x_813_);
v_fold_815_ = lean_uint64_xor(v___x_812_, v___x_814_);
v___x_816_ = 16ULL;
v___x_817_ = lean_uint64_shift_right(v_fold_815_, v___x_816_);
v___x_818_ = lean_uint64_xor(v_fold_815_, v___x_817_);
v___x_819_ = lean_uint64_to_usize(v___x_818_);
v___x_820_ = lean_usize_of_nat(v___x_811_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_sub(v___x_820_, v___x_821_);
v___x_823_ = lean_usize_land(v___x_819_, v___x_822_);
v___x_824_ = lean_array_uget_borrowed(v_x_803_, v___x_823_);
lean_inc(v___x_824_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 2, v___x_824_);
v___x_826_ = v___x_809_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_key_805_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_value_806_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v___x_824_);
v___x_826_ = v_reuseFailAlloc_829_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_array_uset(v_x_803_, v___x_823_, v___x_826_);
v_x_803_ = v___x_827_;
v_x_804_ = v_tail_807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* v_i_831_, lean_object* v_source_832_, lean_object* v_target_833_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_array_get_size(v_source_832_);
v___x_835_ = lean_nat_dec_lt(v_i_831_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_source_832_);
lean_dec(v_i_831_);
return v_target_833_;
}
else
{
lean_object* v_es_836_; lean_object* v___x_837_; lean_object* v_source_838_; lean_object* v_target_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_es_836_ = lean_array_fget(v_source_832_, v_i_831_);
v___x_837_ = lean_box(0);
v_source_838_ = lean_array_fset(v_source_832_, v_i_831_, v___x_837_);
v_target_839_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_833_, v_es_836_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_i_831_, v___x_840_);
lean_dec(v_i_831_);
v_i_831_ = v___x_841_;
v_source_832_ = v_source_838_;
v_target_833_ = v_target_839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* v_data_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_nbuckets_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_844_ = lean_array_get_size(v_data_843_);
v___x_845_ = lean_unsigned_to_nat(2u);
v_nbuckets_846_ = lean_nat_mul(v___x_844_, v___x_845_);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_box(0);
v___x_849_ = lean_mk_array(v_nbuckets_846_, v___x_848_);
v___x_850_ = lean_array_propagate_mark(v_data_843_, v___x_849_);
v___x_851_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_847_, v_data_843_, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_852_, lean_object* v_a_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_size_855_; lean_object* v_buckets_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_899_; 
v_size_855_ = lean_ctor_get(v_m_852_, 0);
v_buckets_856_ = lean_ctor_get(v_m_852_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_m_852_);
if (v_isSharedCheck_899_ == 0)
{
v___x_858_ = v_m_852_;
v_isShared_859_ = v_isSharedCheck_899_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_buckets_856_);
lean_inc(v_size_855_);
lean_dec(v_m_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_899_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v_fold_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v_bkt_873_; uint8_t v___x_874_; 
v___x_860_ = lean_array_get_size(v_buckets_856_);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_853_);
v___x_862_ = 32ULL;
v___x_863_ = lean_uint64_shift_right(v___x_861_, v___x_862_);
v_fold_864_ = lean_uint64_xor(v___x_861_, v___x_863_);
v___x_865_ = 16ULL;
v___x_866_ = lean_uint64_shift_right(v_fold_864_, v___x_865_);
v___x_867_ = lean_uint64_xor(v_fold_864_, v___x_866_);
v___x_868_ = lean_uint64_to_usize(v___x_867_);
v___x_869_ = lean_usize_of_nat(v___x_860_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_sub(v___x_869_, v___x_870_);
v___x_872_ = lean_usize_land(v___x_868_, v___x_871_);
v_bkt_873_ = lean_array_uget_borrowed(v_buckets_856_, v___x_872_);
v___x_874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_853_, v_bkt_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v_size_x27_876_; lean_object* v___x_877_; lean_object* v_buckets_x27_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_875_ = lean_unsigned_to_nat(1u);
v_size_x27_876_ = lean_nat_add(v_size_855_, v___x_875_);
lean_dec(v_size_855_);
lean_inc(v_bkt_873_);
v___x_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_877_, 0, v_a_853_);
lean_ctor_set(v___x_877_, 1, v_b_854_);
lean_ctor_set(v___x_877_, 2, v_bkt_873_);
v_buckets_x27_878_ = lean_array_uset(v_buckets_856_, v___x_872_, v___x_877_);
v___x_879_ = lean_unsigned_to_nat(4u);
v___x_880_ = lean_nat_mul(v_size_x27_876_, v___x_879_);
v___x_881_ = lean_unsigned_to_nat(3u);
v___x_882_ = lean_nat_div(v___x_880_, v___x_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_array_get_size(v_buckets_x27_878_);
v___x_884_ = lean_nat_dec_le(v___x_882_, v___x_883_);
lean_dec(v___x_882_);
if (v___x_884_ == 0)
{
lean_object* v_val_885_; lean_object* v___x_887_; 
v_val_885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_878_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_val_885_);
lean_ctor_set(v___x_858_, 0, v_size_x27_876_);
v___x_887_ = v___x_858_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_size_x27_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_val_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v___x_890_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_buckets_x27_878_);
lean_ctor_set(v___x_858_, 0, v_size_x27_876_);
v___x_890_ = v___x_858_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_size_x27_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_buckets_x27_878_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v___x_892_; lean_object* v_buckets_x27_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
lean_inc(v_bkt_873_);
v___x_892_ = lean_box(0);
v_buckets_x27_893_ = lean_array_uset(v_buckets_856_, v___x_872_, v___x_892_);
v___x_894_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_853_, v_b_854_, v_bkt_873_);
v___x_895_ = lean_array_uset(v_buckets_x27_893_, v___x_872_, v___x_894_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v___x_895_);
v___x_897_ = v___x_858_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_size_855_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
uint8_t v___x_902_; 
v___x_902_ = 0;
return v___x_902_;
}
else
{
lean_object* v_head_903_; lean_object* v_tail_904_; lean_object* v_arg_905_; size_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
v_head_903_ = lean_ctor_get(v_x_901_, 0);
v_tail_904_ = lean_ctor_get(v_x_901_, 1);
v_arg_905_ = lean_ctor_get(v_head_903_, 0);
v___x_906_ = lean_ptr_addr(v_val_900_);
v___x_907_ = lean_ptr_addr(v_arg_905_);
v___x_908_ = lean_usize_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
v_x_901_ = v_tail_904_;
goto _start;
}
else
{
return v___x_908_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_900_ = stack[0].m_obj;
lean_object* v_x_901_ = stack[1].m_obj;
uint8_t v_res_910_;
v_res_910_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_900_, v_x_901_);
stack->m_num = v_res_910_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_911_, lean_object* v_x_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_911_, v_x_912_);
lean_dec(v_x_912_);
lean_dec_ref(v_val_911_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_927_ = l_Lean_Name_append(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_934_, lean_object* v_ctx_935_, lean_object* v___x_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_a_953_; uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec_ref(v___x_936_);
lean_dec_ref(v_ctx_935_);
lean_dec_ref(v_e_934_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_940_);
return v___x_958_;
}
else
{
lean_object* v_snd_959_; lean_object* v_fst_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1072_; 
v_snd_959_ = lean_ctor_get(v_b_940_, 1);
v_fst_960_ = lean_ctor_get(v_b_940_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_b_940_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_962_ = v_b_940_;
v_isShared_963_ = v_isSharedCheck_1072_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_960_);
lean_dec(v_b_940_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1072_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_fst_964_; lean_object* v_snd_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1071_; 
v_fst_964_ = lean_ctor_get(v_snd_959_, 0);
v_snd_965_ = lean_ctor_get(v_snd_959_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_snd_959_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_967_ = v_snd_959_;
v_isShared_968_ = v_isSharedCheck_1071_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_snd_965_);
lean_inc(v_fst_964_);
lean_dec(v_snd_959_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1071_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_map_970_; lean_object* v_candidates_971_; lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_980_ = lean_array_uget_borrowed(v_as_937_, v_i_939_);
v___x_981_ = lean_st_ref_get(v___y_941_);
v___x_982_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_981_, v_a_980_);
lean_dec(v___x_981_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1068_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1068_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_val_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1068_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v_hasTheoryVar_1027_; lean_object* v___x_1028_; 
v_hasTheoryVar_1027_ = lean_ctor_get(v_ctx_935_, 1);
lean_inc_ref(v_hasTheoryVar_1027_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc(v___y_941_);
lean_inc(v_val_983_);
v___x_1028_ = lean_apply_12(v_hasTheoryVar_1027_, v_val_983_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, lean_box(0));
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; uint8_t v___x_1030_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1030_ == 0)
{
lean_del_object(v___x_985_);
lean_dec(v_val_983_);
v_map_970_ = v_fst_960_;
v_candidates_971_ = v_fst_964_;
goto v___jp_969_;
}
else
{
lean_object* v_toCold_1031_; lean_object* v_options_1032_; uint8_t v_hasTrace_1033_; 
v_toCold_1031_ = lean_ctor_get(v___y_949_, 0);
v_options_1032_ = lean_ctor_get(v_toCold_1031_, 2);
v_hasTrace_1033_ = lean_ctor_get_uint8(v_options_1032_, sizeof(void*)*1);
if (v_hasTrace_1033_ == 0)
{
lean_del_object(v___x_985_);
v___y_988_ = v___y_941_;
v___y_989_ = v___y_942_;
v___y_990_ = v___y_943_;
v___y_991_ = v___y_944_;
v___y_992_ = v___y_945_;
v___y_993_ = v___y_946_;
v___y_994_ = v___y_947_;
v___y_995_ = v___y_948_;
v___y_996_ = v___y_949_;
v___y_997_ = v___y_950_;
goto v___jp_987_;
}
else
{
lean_object* v_inheritedTraceOptions_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_inheritedTraceOptions_1034_ = lean_ctor_get(v_toCold_1031_, 11);
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1034_, v_options_1032_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_del_object(v___x_985_);
v___y_988_ = v___y_941_;
v___y_989_ = v___y_942_;
v___y_990_ = v___y_943_;
v___y_991_ = v___y_944_;
v___y_992_ = v___y_945_;
v___y_993_ = v___y_946_;
v___y_994_ = v___y_947_;
v___y_995_ = v___y_948_;
v___y_996_ = v___y_949_;
v___y_997_ = v___y_950_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_inc(v_val_983_);
v___x_1038_ = l_Lean_MessageData_ofExpr(v_val_983_);
v___x_1039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
lean_inc_ref(v___x_936_);
v___x_1041_ = l_Lean_MessageData_ofExpr(v___x_936_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
lean_inc(v_snd_965_);
v___x_1045_ = l_Nat_reprFast(v_snd_965_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 3);
lean_ctor_set(v___x_985_, 0, v___x_1045_);
v___x_1047_ = v___x_985_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = l_Lean_MessageData_ofFormat(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1044_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1035_, v___x_1049_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_dec_ref_known(v___x_1050_, 1);
v___y_988_ = v___y_941_;
v___y_989_ = v___y_942_;
v___y_990_ = v___y_943_;
v___y_991_ = v___y_944_;
v___y_992_ = v___y_945_;
v___y_993_ = v___y_946_;
v___y_994_ = v___y_947_;
v___y_995_ = v___y_948_;
v___y_996_ = v___y_949_;
v___y_997_ = v___y_950_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_val_983_);
lean_del_object(v___x_967_);
lean_dec(v_snd_965_);
lean_dec(v_fst_964_);
lean_del_object(v___x_962_);
lean_dec(v_fst_960_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_ctx_935_);
lean_dec_ref(v_e_934_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
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
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_del_object(v___x_985_);
lean_dec(v_val_983_);
lean_del_object(v___x_967_);
lean_dec(v_snd_965_);
lean_dec(v_fst_964_);
lean_del_object(v___x_962_);
lean_dec(v_fst_960_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_ctx_935_);
lean_dec_ref(v_e_934_);
v_a_1060_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1028_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1028_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
v___jp_987_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_inc_ref_n(v_e_934_, 2);
lean_inc(v_val_983_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_val_983_);
lean_ctor_set(v___x_998_, 1, v_e_934_);
v___x_999_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_934_, v_snd_965_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_960_, v_a_1000_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_val_1002_; uint8_t v___x_1003_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_983_, v_val_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_inc(v_snd_965_);
lean_inc_ref(v___x_998_);
lean_inc_ref(v_ctx_935_);
v___x_1004_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_935_, v_val_983_, v___x_998_, v_snd_965_, v_val_1002_, v_fst_964_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_998_);
lean_ctor_set(v___x_1006_, 1, v_val_1002_);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_960_, v_a_1000_, v___x_1006_);
v_map_970_ = v___x_1007_;
v_candidates_971_ = v_a_1005_;
goto v___jp_969_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_val_1002_);
lean_dec(v_a_1000_);
lean_dec_ref_known(v___x_998_, 2);
lean_del_object(v___x_967_);
lean_dec(v_snd_965_);
lean_del_object(v___x_962_);
lean_dec(v_fst_960_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_ctx_935_);
lean_dec_ref(v_e_934_);
v_a_1008_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1004_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1004_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_dec(v_val_1002_);
lean_dec(v_a_1000_);
lean_dec_ref_known(v___x_998_, 2);
lean_dec(v_val_983_);
v_map_970_ = v_fst_960_;
v_candidates_971_ = v_fst_964_;
goto v___jp_969_;
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v___x_1001_);
lean_dec(v_val_983_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_998_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_960_, v_a_1000_, v___x_1017_);
v_map_970_ = v___x_1018_;
v_candidates_971_ = v_fst_964_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref_known(v___x_998_, 2);
lean_dec(v_val_983_);
lean_del_object(v___x_967_);
lean_dec(v_snd_965_);
lean_dec(v_fst_964_);
lean_del_object(v___x_962_);
lean_dec(v_fst_960_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_ctx_935_);
lean_dec_ref(v_e_934_);
v_a_1019_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_999_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_999_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v___x_982_);
lean_del_object(v___x_967_);
lean_del_object(v___x_962_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_fst_964_);
lean_ctor_set(v___x_1069_, 1, v_snd_965_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_fst_960_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v_a_953_ = v___x_1070_;
goto v___jp_952_;
}
v___jp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_snd_965_, v___x_972_);
lean_dec(v_snd_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_973_);
lean_ctor_set(v___x_967_, 0, v_candidates_971_);
v___x_975_ = v___x_967_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_candidates_971_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_975_);
lean_ctor_set(v___x_962_, 0, v_map_970_);
v___x_977_ = v___x_962_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_map_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
v_a_953_ = v___x_977_;
goto v___jp_952_;
}
}
}
}
}
}
v___jp_952_:
{
size_t v___x_954_; size_t v___x_955_; 
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_939_, v___x_954_);
v_i_939_ = v___x_955_;
v_b_940_ = v_a_953_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_934_ = stack[0].m_obj;
lean_object* v_ctx_935_ = stack[1].m_obj;
lean_object* v___x_936_ = stack[2].m_obj;
lean_object* v_as_937_ = stack[3].m_obj;
size_t v_sz_938_ = stack[4].m_num;
size_t v_i_939_ = stack[5].m_num;
lean_object* v_b_940_ = stack[6].m_obj;
lean_object* v___y_941_ = stack[7].m_obj;
lean_object* v___y_942_ = stack[8].m_obj;
lean_object* v___y_943_ = stack[9].m_obj;
lean_object* v___y_944_ = stack[10].m_obj;
lean_object* v___y_945_ = stack[11].m_obj;
lean_object* v___y_946_ = stack[12].m_obj;
lean_object* v___y_947_ = stack[13].m_obj;
lean_object* v___y_948_ = stack[14].m_obj;
lean_object* v___y_949_ = stack[15].m_obj;
lean_object* v___y_950_ = stack[16].m_obj;
lean_object* v_res_1073_;
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_934_, v_ctx_935_, v___x_936_, v_as_937_, v_sz_938_, v_i_939_, v_b_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1074_ = _args[0];
lean_object* v_ctx_1075_ = _args[1];
lean_object* v___x_1076_ = _args[2];
lean_object* v_as_1077_ = _args[3];
lean_object* v_sz_1078_ = _args[4];
lean_object* v_i_1079_ = _args[5];
lean_object* v_b_1080_ = _args[6];
lean_object* v___y_1081_ = _args[7];
lean_object* v___y_1082_ = _args[8];
lean_object* v___y_1083_ = _args[9];
lean_object* v___y_1084_ = _args[10];
lean_object* v___y_1085_ = _args[11];
lean_object* v___y_1086_ = _args[12];
lean_object* v___y_1087_ = _args[13];
lean_object* v___y_1088_ = _args[14];
lean_object* v___y_1089_ = _args[15];
lean_object* v___y_1090_ = _args[16];
lean_object* v___y_1091_ = _args[17];
_start:
{
size_t v_sz_boxed_1092_; size_t v_i_boxed_1093_; lean_object* v_res_1094_; 
v_sz_boxed_1092_ = lean_unbox_usize(v_sz_1078_);
lean_dec(v_sz_1078_);
v_i_boxed_1093_ = lean_unbox_usize(v_i_1079_);
lean_dec(v_i_1079_);
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1074_, v_ctx_1075_, v___x_1076_, v_as_1077_, v_sz_boxed_1092_, v_i_boxed_1093_, v_b_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v_as_1077_);
return v_res_1094_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1095_, uint8_t v_a_1096_, lean_object* v_as_1097_, size_t v_sz_1098_, size_t v_i_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1099_, v_sz_1098_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v_ctx_1095_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1100_);
return v___x_1113_;
}
else
{
lean_object* v_snd_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1216_; 
v_snd_1114_ = lean_ctor_get(v_b_1100_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_b_1100_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v_b_1100_, 0);
lean_dec(v_unused_1217_);
v___x_1116_ = v_b_1100_;
v_isShared_1117_ = v_isSharedCheck_1216_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snd_1114_);
lean_dec(v_b_1100_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1216_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1215_; 
v_fst_1118_ = lean_ctor_get(v_snd_1114_, 0);
v_snd_1119_ = lean_ctor_get(v_snd_1114_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_snd_1114_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1121_ = v_snd_1114_;
v_isShared_1122_ = v_isSharedCheck_1215_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1119_);
lean_inc(v_fst_1118_);
lean_dec(v_snd_1114_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1215_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v_a_1125_; lean_object* v_a_1138_; uint8_t v___y_1212_; uint8_t v___x_1213_; 
v___x_1123_ = lean_box(0);
v_a_1138_ = lean_array_uget_borrowed(v_as_1097_, v_i_1099_);
v___x_1213_ = l_Lean_Expr_isApp(v_a_1138_);
if (v___x_1213_ == 0)
{
v___y_1212_ = v_a_1096_;
goto v___jp_1211_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = l_Lean_Expr_isEq(v_a_1138_);
if (v___x_1214_ == 0)
{
goto v___jp_1139_;
}
else
{
v___y_1212_ = v_a_1096_;
goto v___jp_1211_;
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_a_1125_);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1127_ = v___x_1121_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_a_1125_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
size_t v___x_1128_; size_t v___x_1129_; 
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1099_, v___x_1128_);
v_i_1099_ = v___x_1129_;
v_b_1100_ = v___x_1127_;
goto _start;
}
}
v___jp_1132_:
{
lean_object* v___x_1134_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v_snd_1119_);
lean_ctor_set(v___x_1116_, 0, v_fst_1118_);
v___x_1134_ = v___x_1116_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_fst_1118_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_snd_1119_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v_a_1125_ = v___x_1134_;
goto v___jp_1124_;
}
}
v___jp_1136_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_fst_1118_);
lean_ctor_set(v___x_1137_, 1, v_snd_1119_);
v_a_1125_ = v___x_1137_;
goto v___jp_1124_;
}
v___jp_1139_:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Lean_Expr_isHEq(v_a_1138_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_inc(v_a_1138_);
v___x_1141_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1138_, v___y_1101_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; uint8_t v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_unbox(v_a_1142_);
lean_dec(v_a_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_del_object(v___x_1116_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_fst_1118_);
lean_ctor_set(v___x_1144_, 1, v_snd_1119_);
v_a_1125_ = v___x_1144_;
goto v___jp_1124_;
}
else
{
lean_object* v_isInterpreted_1145_; lean_object* v___x_1146_; 
v_isInterpreted_1145_ = lean_ctor_get(v_ctx_1095_, 0);
lean_inc_ref(v_isInterpreted_1145_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc(v_a_1138_);
v___x_1146_ = lean_apply_12(v_isInterpreted_1145_, v_a_1138_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, lean_box(0));
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; uint8_t v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l_Lean_Expr_getAppFn(v_a_1138_);
lean_inc_ref(v___x_1149_);
v___x_1150_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1149_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; uint8_t v___x_1152_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = lean_unbox(v_a_1151_);
lean_dec(v_a_1151_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v_dummy_1155_; lean_object* v_nargs_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1116_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v_dummy_1155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1156_ = l_Lean_Expr_getAppNumArgs(v_a_1138_);
lean_inc(v_nargs_1156_);
v___x_1157_ = lean_mk_array(v_nargs_1156_, v_dummy_1155_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_sub(v_nargs_1156_, v___x_1158_);
lean_dec(v_nargs_1156_);
lean_inc_n(v_a_1138_, 2);
v___x_1160_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1138_, v___x_1157_, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_snd_1119_);
lean_ctor_set(v___x_1161_, 1, v___x_1154_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_fst_1118_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v_sz_1163_ = lean_array_size(v___x_1160_);
v___x_1164_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1095_);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1138_, v_ctx_1095_, v___x_1149_, v___x_1160_, v_sz_1163_, v___x_1164_, v___x_1162_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec_ref(v___x_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_snd_1167_; lean_object* v_fst_1168_; lean_object* v_fst_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_snd_1167_ = lean_ctor_get(v_a_1166_, 1);
lean_inc(v_snd_1167_);
v_fst_1168_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_fst_1168_);
lean_dec(v_a_1166_);
v_fst_1169_ = lean_ctor_get(v_snd_1167_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_snd_1167_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v_snd_1167_, 1);
lean_dec(v_unused_1177_);
v___x_1171_ = v_snd_1167_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_fst_1169_);
lean_dec(v_snd_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v_fst_1169_);
lean_ctor_set(v___x_1171_, 0, v_fst_1168_);
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_fst_1168_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_fst_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v_a_1125_ = v___x_1174_;
goto v___jp_1124_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1121_);
lean_dec_ref(v_ctx_1095_);
v_a_1178_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1165_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1165_);
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
lean_dec_ref(v___x_1149_);
goto v___jp_1132_;
}
}
else
{
lean_dec_ref(v___x_1149_);
goto v___jp_1132_;
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v___x_1149_);
lean_del_object(v___x_1121_);
lean_dec(v_snd_1119_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_dec_ref(v_ctx_1095_);
v_a_1186_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1150_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1150_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1194_; 
lean_del_object(v___x_1116_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_fst_1118_);
lean_ctor_set(v___x_1194_, 1, v_snd_1119_);
v_a_1125_ = v___x_1194_;
goto v___jp_1124_;
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1121_);
lean_dec(v_snd_1119_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_dec_ref(v_ctx_1095_);
v_a_1195_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1146_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1146_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_del_object(v___x_1121_);
lean_dec(v_snd_1119_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_dec_ref(v_ctx_1095_);
v_a_1203_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1141_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1141_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_del_object(v___x_1116_);
goto v___jp_1136_;
}
}
v___jp_1211_:
{
if (v___y_1212_ == 0)
{
lean_del_object(v___x_1116_);
goto v___jp_1136_;
}
else
{
goto v___jp_1139_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1095_ = stack[0].m_obj;
uint8_t v_a_1096_ = stack[1].m_num;
lean_object* v_as_1097_ = stack[2].m_obj;
size_t v_sz_1098_ = stack[3].m_num;
size_t v_i_1099_ = stack[4].m_num;
lean_object* v_b_1100_ = stack[5].m_obj;
lean_object* v___y_1101_ = stack[6].m_obj;
lean_object* v___y_1102_ = stack[7].m_obj;
lean_object* v___y_1103_ = stack[8].m_obj;
lean_object* v___y_1104_ = stack[9].m_obj;
lean_object* v___y_1105_ = stack[10].m_obj;
lean_object* v___y_1106_ = stack[11].m_obj;
lean_object* v___y_1107_ = stack[12].m_obj;
lean_object* v___y_1108_ = stack[13].m_obj;
lean_object* v___y_1109_ = stack[14].m_obj;
lean_object* v___y_1110_ = stack[15].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1095_, v_a_1096_, v_as_1097_, v_sz_1098_, v_i_1099_, v_b_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object** _args){
lean_object* v_ctx_1219_ = _args[0];
lean_object* v_a_1220_ = _args[1];
lean_object* v_as_1221_ = _args[2];
lean_object* v_sz_1222_ = _args[3];
lean_object* v_i_1223_ = _args[4];
lean_object* v_b_1224_ = _args[5];
lean_object* v___y_1225_ = _args[6];
lean_object* v___y_1226_ = _args[7];
lean_object* v___y_1227_ = _args[8];
lean_object* v___y_1228_ = _args[9];
lean_object* v___y_1229_ = _args[10];
lean_object* v___y_1230_ = _args[11];
lean_object* v___y_1231_ = _args[12];
lean_object* v___y_1232_ = _args[13];
lean_object* v___y_1233_ = _args[14];
lean_object* v___y_1234_ = _args[15];
lean_object* v___y_1235_ = _args[16];
_start:
{
uint8_t v_a_163007__boxed_1236_; size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_a_163007__boxed_1236_ = lean_unbox(v_a_1220_);
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1222_);
lean_dec(v_sz_1222_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1223_);
lean_dec(v_i_1223_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1219_, v_a_163007__boxed_1236_, v_as_1221_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v_as_1221_);
return v_res_1239_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1240_, uint8_t v_a_1241_, lean_object* v_as_1242_, size_t v_sz_1243_, size_t v_i_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1244_, v_sz_1243_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_ctx_1240_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_b_1245_);
return v___x_1258_;
}
else
{
lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1361_; 
v_snd_1259_ = lean_ctor_get(v_b_1245_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_b_1245_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_b_1245_, 0);
lean_dec(v_unused_1362_);
v___x_1261_ = v_b_1245_;
v_isShared_1262_ = v_isSharedCheck_1361_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_dec(v_b_1245_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1361_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1360_; 
v_fst_1263_ = lean_ctor_get(v_snd_1259_, 0);
v_snd_1264_ = lean_ctor_get(v_snd_1259_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_snd_1259_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1266_ = v_snd_1259_;
v_isShared_1267_ = v_isSharedCheck_1360_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v_snd_1259_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1360_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v_a_1270_; lean_object* v_a_1283_; uint8_t v___y_1357_; uint8_t v___x_1358_; 
v___x_1268_ = lean_box(0);
v_a_1283_ = lean_array_uget_borrowed(v_as_1242_, v_i_1244_);
v___x_1358_ = l_Lean_Expr_isApp(v_a_1283_);
if (v___x_1358_ == 0)
{
v___y_1357_ = v_a_1241_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Expr_isEq(v_a_1283_);
if (v___x_1359_ == 0)
{
goto v___jp_1284_;
}
else
{
v___y_1357_ = v_a_1241_;
goto v___jp_1356_;
}
}
v___jp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_a_1270_);
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_a_1270_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1244_, v___x_1273_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1240_, v_a_1241_, v_as_1242_, v_sz_1243_, v___x_1274_, v___x_1272_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1275_;
}
}
v___jp_1277_:
{
lean_object* v___x_1279_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_snd_1264_);
lean_ctor_set(v___x_1261_, 0, v_fst_1263_);
v___x_1279_ = v___x_1261_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_fst_1263_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_snd_1264_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v_a_1270_ = v___x_1279_;
goto v___jp_1269_;
}
}
v___jp_1281_:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_fst_1263_);
lean_ctor_set(v___x_1282_, 1, v_snd_1264_);
v_a_1270_ = v___x_1282_;
goto v___jp_1269_;
}
v___jp_1284_:
{
uint8_t v___x_1285_; 
v___x_1285_ = l_Lean_Expr_isHEq(v_a_1283_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_inc(v_a_1283_);
v___x_1286_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1283_, v___y_1246_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_del_object(v___x_1261_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_fst_1263_);
lean_ctor_set(v___x_1289_, 1, v_snd_1264_);
v_a_1270_ = v___x_1289_;
goto v___jp_1269_;
}
else
{
lean_object* v_isInterpreted_1290_; lean_object* v___x_1291_; 
v_isInterpreted_1290_ = lean_ctor_get(v_ctx_1240_, 0);
lean_inc_ref(v_isInterpreted_1290_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc(v_a_1283_);
v___x_1291_ = lean_apply_12(v_isInterpreted_1290_, v_a_1283_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; uint8_t v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = lean_unbox(v_a_1292_);
lean_dec(v_a_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = l_Lean_Expr_getAppFn(v_a_1283_);
lean_inc_ref(v___x_1294_);
v___x_1295_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1294_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; uint8_t v___x_1297_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1294_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v_dummy_1300_; lean_object* v_nargs_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; size_t v_sz_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1261_);
v___x_1299_ = lean_unsigned_to_nat(0u);
v_dummy_1300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1301_ = l_Lean_Expr_getAppNumArgs(v_a_1283_);
lean_inc(v_nargs_1301_);
v___x_1302_ = lean_mk_array(v_nargs_1301_, v_dummy_1300_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_nat_sub(v_nargs_1301_, v___x_1303_);
lean_dec(v_nargs_1301_);
lean_inc_n(v_a_1283_, 2);
v___x_1305_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1283_, v___x_1302_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_snd_1264_);
lean_ctor_set(v___x_1306_, 1, v___x_1299_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_fst_1263_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v_sz_1308_ = lean_array_size(v___x_1305_);
v___x_1309_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1240_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1283_, v_ctx_1240_, v___x_1294_, v___x_1305_, v_sz_1308_, v___x_1309_, v___x_1307_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec_ref(v___x_1305_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v_snd_1312_; lean_object* v_fst_1313_; lean_object* v_fst_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v_snd_1312_ = lean_ctor_get(v_a_1311_, 1);
lean_inc(v_snd_1312_);
v_fst_1313_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_fst_1313_);
lean_dec(v_a_1311_);
v_fst_1314_ = lean_ctor_get(v_snd_1312_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_snd_1312_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_snd_1312_, 1);
lean_dec(v_unused_1322_);
v___x_1316_ = v_snd_1312_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_fst_1314_);
lean_dec(v_snd_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_fst_1314_);
lean_ctor_set(v___x_1316_, 0, v_fst_1313_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_fst_1313_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_fst_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
v_a_1270_ = v___x_1319_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_del_object(v___x_1266_);
lean_dec_ref(v_ctx_1240_);
v_a_1323_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1310_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1310_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_dec_ref(v___x_1294_);
goto v___jp_1277_;
}
}
else
{
lean_dec_ref(v___x_1294_);
goto v___jp_1277_;
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v___x_1294_);
lean_del_object(v___x_1266_);
lean_dec(v_snd_1264_);
lean_dec(v_fst_1263_);
lean_del_object(v___x_1261_);
lean_dec_ref(v_ctx_1240_);
v_a_1331_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1295_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1295_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v___x_1339_; 
lean_del_object(v___x_1261_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_fst_1263_);
lean_ctor_set(v___x_1339_, 1, v_snd_1264_);
v_a_1270_ = v___x_1339_;
goto v___jp_1269_;
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_del_object(v___x_1266_);
lean_dec(v_snd_1264_);
lean_dec(v_fst_1263_);
lean_del_object(v___x_1261_);
lean_dec_ref(v_ctx_1240_);
v_a_1340_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1291_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1291_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_del_object(v___x_1266_);
lean_dec(v_snd_1264_);
lean_dec(v_fst_1263_);
lean_del_object(v___x_1261_);
lean_dec_ref(v_ctx_1240_);
v_a_1348_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1286_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1286_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_del_object(v___x_1261_);
goto v___jp_1281_;
}
}
v___jp_1356_:
{
if (v___y_1357_ == 0)
{
lean_del_object(v___x_1261_);
goto v___jp_1281_;
}
else
{
goto v___jp_1284_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1240_ = stack[0].m_obj;
uint8_t v_a_1241_ = stack[1].m_num;
lean_object* v_as_1242_ = stack[2].m_obj;
size_t v_sz_1243_ = stack[3].m_num;
size_t v_i_1244_ = stack[4].m_num;
lean_object* v_b_1245_ = stack[5].m_obj;
lean_object* v___y_1246_ = stack[6].m_obj;
lean_object* v___y_1247_ = stack[7].m_obj;
lean_object* v___y_1248_ = stack[8].m_obj;
lean_object* v___y_1249_ = stack[9].m_obj;
lean_object* v___y_1250_ = stack[10].m_obj;
lean_object* v___y_1251_ = stack[11].m_obj;
lean_object* v___y_1252_ = stack[12].m_obj;
lean_object* v___y_1253_ = stack[13].m_obj;
lean_object* v___y_1254_ = stack[14].m_obj;
lean_object* v___y_1255_ = stack[15].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1240_, v_a_1241_, v_as_1242_, v_sz_1243_, v_i_1244_, v_b_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args){
lean_object* v_ctx_1364_ = _args[0];
lean_object* v_a_1365_ = _args[1];
lean_object* v_as_1366_ = _args[2];
lean_object* v_sz_1367_ = _args[3];
lean_object* v_i_1368_ = _args[4];
lean_object* v_b_1369_ = _args[5];
lean_object* v___y_1370_ = _args[6];
lean_object* v___y_1371_ = _args[7];
lean_object* v___y_1372_ = _args[8];
lean_object* v___y_1373_ = _args[9];
lean_object* v___y_1374_ = _args[10];
lean_object* v___y_1375_ = _args[11];
lean_object* v___y_1376_ = _args[12];
lean_object* v___y_1377_ = _args[13];
lean_object* v___y_1378_ = _args[14];
lean_object* v___y_1379_ = _args[15];
lean_object* v___y_1380_ = _args[16];
_start:
{
uint8_t v_a_163354__boxed_1381_; size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_a_163354__boxed_1381_ = lean_unbox(v_a_1365_);
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1367_);
lean_dec(v_sz_1367_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1368_);
lean_dec(v_i_1368_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1364_, v_a_163354__boxed_1381_, v_as_1366_, v_sz_boxed_1382_, v_i_boxed_1383_, v_b_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v_as_1366_);
return v_res_1384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1385_, uint8_t v_a_1386_, lean_object* v_as_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_usize_dec_lt(v_i_1389_, v_sz_1388_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
lean_dec_ref(v_ctx_1385_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_b_1390_);
return v___x_1403_;
}
else
{
lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1506_; 
v_snd_1404_ = lean_ctor_get(v_b_1390_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_b_1390_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_b_1390_, 0);
lean_dec(v_unused_1507_);
v___x_1406_ = v_b_1390_;
v_isShared_1407_ = v_isSharedCheck_1506_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_dec(v_b_1390_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1506_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_fst_1408_; lean_object* v_snd_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1505_; 
v_fst_1408_ = lean_ctor_get(v_snd_1404_, 0);
v_snd_1409_ = lean_ctor_get(v_snd_1404_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_snd_1404_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1411_ = v_snd_1404_;
v_isShared_1412_ = v_isSharedCheck_1505_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_snd_1409_);
lean_inc(v_fst_1408_);
lean_dec(v_snd_1404_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1505_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v_a_1415_; lean_object* v_a_1428_; uint8_t v___y_1502_; uint8_t v___x_1503_; 
v___x_1413_ = lean_box(0);
v_a_1428_ = lean_array_uget_borrowed(v_as_1387_, v_i_1389_);
v___x_1503_ = l_Lean_Expr_isApp(v_a_1428_);
if (v___x_1503_ == 0)
{
v___y_1502_ = v_a_1386_;
goto v___jp_1501_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = l_Lean_Expr_isEq(v_a_1428_);
if (v___x_1504_ == 0)
{
goto v___jp_1429_;
}
else
{
v___y_1502_ = v_a_1386_;
goto v___jp_1501_;
}
}
v___jp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v_a_1415_);
lean_ctor_set(v___x_1411_, 0, v___x_1413_);
v___x_1417_ = v___x_1411_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_a_1415_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
size_t v___x_1418_; size_t v___x_1419_; 
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1389_, v___x_1418_);
v_i_1389_ = v___x_1419_;
v_b_1390_ = v___x_1417_;
goto _start;
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_snd_1409_);
lean_ctor_set(v___x_1406_, 0, v_fst_1408_);
v___x_1424_ = v___x_1406_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1408_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_snd_1409_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
v_a_1415_ = v___x_1424_;
goto v___jp_1414_;
}
}
v___jp_1426_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_fst_1408_);
lean_ctor_set(v___x_1427_, 1, v_snd_1409_);
v_a_1415_ = v___x_1427_;
goto v___jp_1414_;
}
v___jp_1429_:
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Lean_Expr_isHEq(v_a_1428_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_inc(v_a_1428_);
v___x_1431_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1428_, v___y_1391_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_del_object(v___x_1406_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_fst_1408_);
lean_ctor_set(v___x_1434_, 1, v_snd_1409_);
v_a_1415_ = v___x_1434_;
goto v___jp_1414_;
}
else
{
lean_object* v_isInterpreted_1435_; lean_object* v___x_1436_; 
v_isInterpreted_1435_ = lean_ctor_get(v_ctx_1385_, 0);
lean_inc_ref(v_isInterpreted_1435_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v_a_1428_);
v___x_1436_ = lean_apply_12(v_isInterpreted_1435_, v_a_1428_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, lean_box(0));
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; uint8_t v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = lean_unbox(v_a_1437_);
lean_dec(v_a_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = l_Lean_Expr_getAppFn(v_a_1428_);
lean_inc_ref(v___x_1439_);
v___x_1440_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1439_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; uint8_t v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_unbox(v_a_1441_);
lean_dec(v_a_1441_);
if (v___x_1442_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1439_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v_dummy_1445_; lean_object* v_nargs_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
lean_del_object(v___x_1406_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v_dummy_1445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1446_ = l_Lean_Expr_getAppNumArgs(v_a_1428_);
lean_inc(v_nargs_1446_);
v___x_1447_ = lean_mk_array(v_nargs_1446_, v_dummy_1445_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_sub(v_nargs_1446_, v___x_1448_);
lean_dec(v_nargs_1446_);
lean_inc_n(v_a_1428_, 2);
v___x_1450_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1428_, v___x_1447_, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_snd_1409_);
lean_ctor_set(v___x_1451_, 1, v___x_1444_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_fst_1408_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v_sz_1453_ = lean_array_size(v___x_1450_);
v___x_1454_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1385_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1428_, v_ctx_1385_, v___x_1439_, v___x_1450_, v_sz_1453_, v___x_1454_, v___x_1452_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec_ref(v___x_1450_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v_snd_1457_; lean_object* v_fst_1458_; lean_object* v_fst_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v_snd_1457_ = lean_ctor_get(v_a_1456_, 1);
lean_inc(v_snd_1457_);
v_fst_1458_ = lean_ctor_get(v_a_1456_, 0);
lean_inc(v_fst_1458_);
lean_dec(v_a_1456_);
v_fst_1459_ = lean_ctor_get(v_snd_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_snd_1457_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_snd_1457_, 1);
lean_dec(v_unused_1467_);
v___x_1461_ = v_snd_1457_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_fst_1459_);
lean_dec(v_snd_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v_fst_1459_);
lean_ctor_set(v___x_1461_, 0, v_fst_1458_);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_fst_1458_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_fst_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_a_1415_ = v___x_1464_;
goto v___jp_1414_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1411_);
lean_dec_ref(v_ctx_1385_);
v_a_1468_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1455_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1455_);
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
lean_dec_ref(v___x_1439_);
goto v___jp_1422_;
}
}
else
{
lean_dec_ref(v___x_1439_);
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___x_1439_);
lean_del_object(v___x_1411_);
lean_dec(v_snd_1409_);
lean_dec(v_fst_1408_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_ctx_1385_);
v_a_1476_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1440_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1440_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1484_; 
lean_del_object(v___x_1406_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_fst_1408_);
lean_ctor_set(v___x_1484_, 1, v_snd_1409_);
v_a_1415_ = v___x_1484_;
goto v___jp_1414_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_del_object(v___x_1411_);
lean_dec(v_snd_1409_);
lean_dec(v_fst_1408_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_ctx_1385_);
v_a_1485_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1436_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1436_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1411_);
lean_dec(v_snd_1409_);
lean_dec(v_fst_1408_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_ctx_1385_);
v_a_1493_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1431_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1431_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_del_object(v___x_1406_);
goto v___jp_1426_;
}
}
v___jp_1501_:
{
if (v___y_1502_ == 0)
{
lean_del_object(v___x_1406_);
goto v___jp_1426_;
}
else
{
goto v___jp_1429_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1385_ = stack[0].m_obj;
uint8_t v_a_1386_ = stack[1].m_num;
lean_object* v_as_1387_ = stack[2].m_obj;
size_t v_sz_1388_ = stack[3].m_num;
size_t v_i_1389_ = stack[4].m_num;
lean_object* v_b_1390_ = stack[5].m_obj;
lean_object* v___y_1391_ = stack[6].m_obj;
lean_object* v___y_1392_ = stack[7].m_obj;
lean_object* v___y_1393_ = stack[8].m_obj;
lean_object* v___y_1394_ = stack[9].m_obj;
lean_object* v___y_1395_ = stack[10].m_obj;
lean_object* v___y_1396_ = stack[11].m_obj;
lean_object* v___y_1397_ = stack[12].m_obj;
lean_object* v___y_1398_ = stack[13].m_obj;
lean_object* v___y_1399_ = stack[14].m_obj;
lean_object* v___y_1400_ = stack[15].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1385_, v_a_1386_, v_as_1387_, v_sz_1388_, v_i_1389_, v_b_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object** _args){
lean_object* v_ctx_1509_ = _args[0];
lean_object* v_a_1510_ = _args[1];
lean_object* v_as_1511_ = _args[2];
lean_object* v_sz_1512_ = _args[3];
lean_object* v_i_1513_ = _args[4];
lean_object* v_b_1514_ = _args[5];
lean_object* v___y_1515_ = _args[6];
lean_object* v___y_1516_ = _args[7];
lean_object* v___y_1517_ = _args[8];
lean_object* v___y_1518_ = _args[9];
lean_object* v___y_1519_ = _args[10];
lean_object* v___y_1520_ = _args[11];
lean_object* v___y_1521_ = _args[12];
lean_object* v___y_1522_ = _args[13];
lean_object* v___y_1523_ = _args[14];
lean_object* v___y_1524_ = _args[15];
lean_object* v___y_1525_ = _args[16];
_start:
{
uint8_t v_a_163701__boxed_1526_; size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_a_163701__boxed_1526_ = lean_unbox(v_a_1510_);
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1512_);
lean_dec(v_sz_1512_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1509_, v_a_163701__boxed_1526_, v_as_1511_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v_as_1511_);
return v_res_1529_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1530_, uint8_t v_a_1531_, lean_object* v_as_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_usize_dec_lt(v_i_1534_, v_sz_1533_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref(v_ctx_1530_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_b_1535_);
return v___x_1548_;
}
else
{
lean_object* v_snd_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1651_; 
v_snd_1549_ = lean_ctor_get(v_b_1535_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_b_1535_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v_b_1535_, 0);
lean_dec(v_unused_1652_);
v___x_1551_ = v_b_1535_;
v_isShared_1552_ = v_isSharedCheck_1651_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_snd_1549_);
lean_dec(v_b_1535_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1651_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1650_; 
v_fst_1553_ = lean_ctor_get(v_snd_1549_, 0);
v_snd_1554_ = lean_ctor_get(v_snd_1549_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_snd_1549_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1556_ = v_snd_1549_;
v_isShared_1557_ = v_isSharedCheck_1650_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_snd_1554_);
lean_inc(v_fst_1553_);
lean_dec(v_snd_1549_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1650_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v_a_1560_; lean_object* v_a_1573_; uint8_t v___y_1647_; uint8_t v___x_1648_; 
v___x_1558_ = lean_box(0);
v_a_1573_ = lean_array_uget_borrowed(v_as_1532_, v_i_1534_);
v___x_1648_ = l_Lean_Expr_isApp(v_a_1573_);
if (v___x_1648_ == 0)
{
v___y_1647_ = v_a_1531_;
goto v___jp_1646_;
}
else
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Lean_Expr_isEq(v_a_1573_);
if (v___x_1649_ == 0)
{
goto v___jp_1574_;
}
else
{
v___y_1647_ = v_a_1531_;
goto v___jp_1646_;
}
}
v___jp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v_a_1560_);
lean_ctor_set(v___x_1556_, 0, v___x_1558_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1560_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = ((size_t)1ULL);
v___x_1564_ = lean_usize_add(v_i_1534_, v___x_1563_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1530_, v_a_1531_, v_as_1532_, v_sz_1533_, v___x_1564_, v___x_1562_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1565_;
}
}
v___jp_1567_:
{
lean_object* v___x_1569_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v_snd_1554_);
lean_ctor_set(v___x_1551_, 0, v_fst_1553_);
v___x_1569_ = v___x_1551_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_fst_1553_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1554_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_a_1560_ = v___x_1569_;
goto v___jp_1559_;
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_fst_1553_);
lean_ctor_set(v___x_1572_, 1, v_snd_1554_);
v_a_1560_ = v___x_1572_;
goto v___jp_1559_;
}
v___jp_1574_:
{
uint8_t v___x_1575_; 
v___x_1575_ = l_Lean_Expr_isHEq(v_a_1573_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_inc(v_a_1573_);
v___x_1576_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1573_, v___y_1536_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; uint8_t v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_unbox(v_a_1577_);
lean_dec(v_a_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_del_object(v___x_1551_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_fst_1553_);
lean_ctor_set(v___x_1579_, 1, v_snd_1554_);
v_a_1560_ = v___x_1579_;
goto v___jp_1559_;
}
else
{
lean_object* v_isInterpreted_1580_; lean_object* v___x_1581_; 
v_isInterpreted_1580_ = lean_ctor_get(v_ctx_1530_, 0);
lean_inc_ref(v_isInterpreted_1580_);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc(v_a_1573_);
v___x_1581_ = lean_apply_12(v_isInterpreted_1580_, v_a_1573_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = l_Lean_Expr_getAppFn(v_a_1573_);
lean_inc_ref(v___x_1584_);
v___x_1585_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1584_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_unbox(v_a_1586_);
lean_dec(v_a_1586_);
if (v___x_1587_ == 0)
{
uint8_t v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1584_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v_dummy_1590_; lean_object* v_nargs_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
lean_del_object(v___x_1551_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v_dummy_1590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1591_ = l_Lean_Expr_getAppNumArgs(v_a_1573_);
lean_inc(v_nargs_1591_);
v___x_1592_ = lean_mk_array(v_nargs_1591_, v_dummy_1590_);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_sub(v_nargs_1591_, v___x_1593_);
lean_dec(v_nargs_1591_);
lean_inc_n(v_a_1573_, 2);
v___x_1595_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1573_, v___x_1592_, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_snd_1554_);
lean_ctor_set(v___x_1596_, 1, v___x_1589_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_fst_1553_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v_sz_1598_ = lean_array_size(v___x_1595_);
v___x_1599_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1530_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1573_, v_ctx_1530_, v___x_1584_, v___x_1595_, v_sz_1598_, v___x_1599_, v___x_1597_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec_ref(v___x_1595_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v_snd_1602_; lean_object* v_fst_1603_; lean_object* v_fst_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v_snd_1602_ = lean_ctor_get(v_a_1601_, 1);
lean_inc(v_snd_1602_);
v_fst_1603_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_fst_1603_);
lean_dec(v_a_1601_);
v_fst_1604_ = lean_ctor_get(v_snd_1602_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_snd_1602_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_snd_1602_, 1);
lean_dec(v_unused_1612_);
v___x_1606_ = v_snd_1602_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_fst_1604_);
lean_dec(v_snd_1602_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v_fst_1604_);
lean_ctor_set(v___x_1606_, 0, v_fst_1603_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fst_1603_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_fst_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_a_1560_ = v___x_1609_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_del_object(v___x_1556_);
lean_dec_ref(v_ctx_1530_);
v_a_1613_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1600_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1600_);
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
lean_dec_ref(v___x_1584_);
goto v___jp_1567_;
}
}
else
{
lean_dec_ref(v___x_1584_);
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___x_1584_);
lean_del_object(v___x_1556_);
lean_dec(v_snd_1554_);
lean_dec(v_fst_1553_);
lean_del_object(v___x_1551_);
lean_dec_ref(v_ctx_1530_);
v_a_1621_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1585_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1585_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1629_; 
lean_del_object(v___x_1551_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_fst_1553_);
lean_ctor_set(v___x_1629_, 1, v_snd_1554_);
v_a_1560_ = v___x_1629_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_del_object(v___x_1556_);
lean_dec(v_snd_1554_);
lean_dec(v_fst_1553_);
lean_del_object(v___x_1551_);
lean_dec_ref(v_ctx_1530_);
v_a_1630_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1581_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1581_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_del_object(v___x_1556_);
lean_dec(v_snd_1554_);
lean_dec(v_fst_1553_);
lean_del_object(v___x_1551_);
lean_dec_ref(v_ctx_1530_);
v_a_1638_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1576_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1576_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_del_object(v___x_1551_);
goto v___jp_1571_;
}
}
v___jp_1646_:
{
if (v___y_1647_ == 0)
{
lean_del_object(v___x_1551_);
goto v___jp_1571_;
}
else
{
goto v___jp_1574_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1530_ = stack[0].m_obj;
uint8_t v_a_1531_ = stack[1].m_num;
lean_object* v_as_1532_ = stack[2].m_obj;
size_t v_sz_1533_ = stack[3].m_num;
size_t v_i_1534_ = stack[4].m_num;
lean_object* v_b_1535_ = stack[5].m_obj;
lean_object* v___y_1536_ = stack[6].m_obj;
lean_object* v___y_1537_ = stack[7].m_obj;
lean_object* v___y_1538_ = stack[8].m_obj;
lean_object* v___y_1539_ = stack[9].m_obj;
lean_object* v___y_1540_ = stack[10].m_obj;
lean_object* v___y_1541_ = stack[11].m_obj;
lean_object* v___y_1542_ = stack[12].m_obj;
lean_object* v___y_1543_ = stack[13].m_obj;
lean_object* v___y_1544_ = stack[14].m_obj;
lean_object* v___y_1545_ = stack[15].m_obj;
lean_object* v_res_1653_;
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1530_, v_a_1531_, v_as_1532_, v_sz_1533_, v_i_1534_, v_b_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
stack->m_obj
 = v_res_1653_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object** _args){
lean_object* v_ctx_1654_ = _args[0];
lean_object* v_a_1655_ = _args[1];
lean_object* v_as_1656_ = _args[2];
lean_object* v_sz_1657_ = _args[3];
lean_object* v_i_1658_ = _args[4];
lean_object* v_b_1659_ = _args[5];
lean_object* v___y_1660_ = _args[6];
lean_object* v___y_1661_ = _args[7];
lean_object* v___y_1662_ = _args[8];
lean_object* v___y_1663_ = _args[9];
lean_object* v___y_1664_ = _args[10];
lean_object* v___y_1665_ = _args[11];
lean_object* v___y_1666_ = _args[12];
lean_object* v___y_1667_ = _args[13];
lean_object* v___y_1668_ = _args[14];
lean_object* v___y_1669_ = _args[15];
lean_object* v___y_1670_ = _args[16];
_start:
{
uint8_t v_a_164048__boxed_1671_; size_t v_sz_boxed_1672_; size_t v_i_boxed_1673_; lean_object* v_res_1674_; 
v_a_164048__boxed_1671_ = lean_unbox(v_a_1655_);
v_sz_boxed_1672_ = lean_unbox_usize(v_sz_1657_);
lean_dec(v_sz_1657_);
v_i_boxed_1673_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1654_, v_a_164048__boxed_1671_, v_as_1656_, v_sz_boxed_1672_, v_i_boxed_1673_, v_b_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v_as_1656_);
return v_res_1674_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1675_, lean_object* v_ctx_1676_, uint8_t v_a_1677_, lean_object* v_n_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
if (lean_obj_tag(v_n_1678_) == 0)
{
lean_object* v_cs_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v_cs_1691_ = lean_ctor_get(v_n_1678_, 0);
v___x_1692_ = lean_box(0);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_b_1679_);
v_sz_1694_ = lean_array_size(v_cs_1691_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1675_, v_ctx_1676_, v_a_1677_, v_cs_1691_, v_sz_1694_, v___x_1695_, v___x_1693_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
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
else
{
lean_object* v_vs_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; size_t v_sz_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v_vs_1720_ = lean_ctor_get(v_n_1678_, 0);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_b_1679_);
v_sz_1723_ = lean_array_size(v_vs_1720_);
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1676_, v_a_1677_, v_vs_1720_, v_sz_1723_, v___x_1724_, v___x_1722_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1740_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_fst_1730_; 
v_fst_1730_ = lean_ctor_get(v_a_1726_, 0);
if (lean_obj_tag(v_fst_1730_) == 0)
{
lean_object* v_snd_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v_snd_1731_ = lean_ctor_get(v_a_1726_, 1);
lean_inc(v_snd_1731_);
lean_dec(v_a_1726_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_snd_1731_);
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
else
{
lean_object* v_val_1736_; lean_object* v___x_1738_; 
lean_inc_ref(v_fst_1730_);
lean_dec(v_a_1726_);
v_val_1736_ = lean_ctor_get(v_fst_1730_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v_fst_1730_, 1);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_val_1736_);
v___x_1738_ = v___x_1728_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_val_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_a_1741_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1725_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1725_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1675_ = stack[0].m_obj;
lean_object* v_ctx_1676_ = stack[1].m_obj;
uint8_t v_a_1677_ = stack[2].m_num;
lean_object* v_n_1678_ = stack[3].m_obj;
lean_object* v_b_1679_ = stack[4].m_obj;
lean_object* v___y_1680_ = stack[5].m_obj;
lean_object* v___y_1681_ = stack[6].m_obj;
lean_object* v___y_1682_ = stack[7].m_obj;
lean_object* v___y_1683_ = stack[8].m_obj;
lean_object* v___y_1684_ = stack[9].m_obj;
lean_object* v___y_1685_ = stack[10].m_obj;
lean_object* v___y_1686_ = stack[11].m_obj;
lean_object* v___y_1687_ = stack[12].m_obj;
lean_object* v___y_1688_ = stack[13].m_obj;
lean_object* v___y_1689_ = stack[14].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1675_, v_ctx_1676_, v_a_1677_, v_n_1678_, v_b_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
stack->m_obj
 = v_res_1749_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1750_, lean_object* v_ctx_1751_, uint8_t v_a_1752_, lean_object* v_as_1753_, size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref(v_ctx_1751_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_b_1756_);
return v___x_1769_;
}
else
{
lean_object* v_snd_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1804_; 
v_snd_1770_ = lean_ctor_get(v_b_1756_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_b_1756_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_b_1756_, 0);
lean_dec(v_unused_1805_);
v___x_1772_ = v_b_1756_;
v_isShared_1773_ = v_isSharedCheck_1804_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snd_1770_);
lean_dec(v_b_1756_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1804_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
v_a_1775_ = lean_array_uget_borrowed(v_as_1753_, v_i_1755_);
lean_inc(v_snd_1770_);
lean_inc_ref(v_ctx_1751_);
v___x_1776_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1750_, v_ctx_1751_, v_a_1752_, v_a_1775_, v_snd_1770_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1795_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1795_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1795_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
if (lean_obj_tag(v_a_1777_) == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec_ref(v_ctx_1751_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_a_1777_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1781_);
v___x_1783_ = v___x_1772_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_snd_1770_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1783_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1770_);
v_a_1788_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v_a_1777_, 1);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_a_1788_);
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1790_ = v___x_1772_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1788_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
size_t v___x_1791_; size_t v___x_1792_; 
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1755_, v___x_1791_);
v_i_1755_ = v___x_1792_;
v_b_1756_ = v___x_1790_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_del_object(v___x_1772_);
lean_dec(v_snd_1770_);
lean_dec_ref(v_ctx_1751_);
v_a_1796_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1776_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1776_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1750_ = stack[0].m_obj;
lean_object* v_ctx_1751_ = stack[1].m_obj;
uint8_t v_a_1752_ = stack[2].m_num;
lean_object* v_as_1753_ = stack[3].m_obj;
size_t v_sz_1754_ = stack[4].m_num;
size_t v_i_1755_ = stack[5].m_num;
lean_object* v_b_1756_ = stack[6].m_obj;
lean_object* v___y_1757_ = stack[7].m_obj;
lean_object* v___y_1758_ = stack[8].m_obj;
lean_object* v___y_1759_ = stack[9].m_obj;
lean_object* v___y_1760_ = stack[10].m_obj;
lean_object* v___y_1761_ = stack[11].m_obj;
lean_object* v___y_1762_ = stack[12].m_obj;
lean_object* v___y_1763_ = stack[13].m_obj;
lean_object* v___y_1764_ = stack[14].m_obj;
lean_object* v___y_1765_ = stack[15].m_obj;
lean_object* v___y_1766_ = stack[16].m_obj;
lean_object* v_res_1806_;
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1750_, v_ctx_1751_, v_a_1752_, v_as_1753_, v_sz_1754_, v_i_1755_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
stack->m_obj
 = v_res_1806_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1807_ = _args[0];
lean_object* v_ctx_1808_ = _args[1];
lean_object* v_a_1809_ = _args[2];
lean_object* v_as_1810_ = _args[3];
lean_object* v_sz_1811_ = _args[4];
lean_object* v_i_1812_ = _args[5];
lean_object* v_b_1813_ = _args[6];
lean_object* v___y_1814_ = _args[7];
lean_object* v___y_1815_ = _args[8];
lean_object* v___y_1816_ = _args[9];
lean_object* v___y_1817_ = _args[10];
lean_object* v___y_1818_ = _args[11];
lean_object* v___y_1819_ = _args[12];
lean_object* v___y_1820_ = _args[13];
lean_object* v___y_1821_ = _args[14];
lean_object* v___y_1822_ = _args[15];
lean_object* v___y_1823_ = _args[16];
lean_object* v___y_1824_ = _args[17];
_start:
{
uint8_t v_a_164394__boxed_1825_; size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; lean_object* v_res_1828_; 
v_a_164394__boxed_1825_ = lean_unbox(v_a_1809_);
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1811_);
lean_dec(v_sz_1811_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1812_);
lean_dec(v_i_1812_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1807_, v_ctx_1808_, v_a_164394__boxed_1825_, v_as_1810_, v_sz_boxed_1826_, v_i_boxed_1827_, v_b_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v_as_1810_);
lean_dec_ref(v_init_1807_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1829_, lean_object* v_ctx_1830_, lean_object* v_a_1831_, lean_object* v_n_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v_a_164422__boxed_1845_; lean_object* v_res_1846_; 
v_a_164422__boxed_1845_ = lean_unbox(v_a_1831_);
v_res_1846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1829_, v_ctx_1830_, v_a_164422__boxed_1845_, v_n_1832_, v_b_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v_n_1832_);
lean_dec_ref(v_init_1829_);
return v_res_1846_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1847_, uint8_t v_a_1848_, lean_object* v_t_1849_, lean_object* v_init_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_root_1862_; lean_object* v_tail_1863_; lean_object* v___x_1864_; 
v_root_1862_ = lean_ctor_get(v_t_1849_, 0);
v_tail_1863_ = lean_ctor_get(v_t_1849_, 1);
lean_inc_ref(v_ctx_1847_);
lean_inc_ref(v_init_1850_);
v___x_1864_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1850_, v_ctx_1847_, v_a_1848_, v_root_1862_, v_init_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec_ref(v_init_1850_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1901_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
if (lean_obj_tag(v_a_1865_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v_ctx_1847_);
v_a_1869_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v_a_1865_, 1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_a_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; 
lean_del_object(v___x_1867_);
v_a_1873_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v_a_1865_, 1);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1873_);
v_sz_1876_ = lean_array_size(v_tail_1863_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1847_, v_a_1848_, v_tail_1863_, v_sz_1876_, v___x_1877_, v___x_1875_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1892_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_fst_1883_; 
v_fst_1883_ = lean_ctor_get(v_a_1879_, 0);
if (lean_obj_tag(v_fst_1883_) == 0)
{
lean_object* v_snd_1884_; lean_object* v___x_1886_; 
v_snd_1884_ = lean_ctor_get(v_a_1879_, 1);
lean_inc(v_snd_1884_);
lean_dec(v_a_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_snd_1884_);
v___x_1886_ = v___x_1881_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_snd_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; 
lean_inc_ref(v_fst_1883_);
lean_dec(v_a_1879_);
v_val_1888_ = lean_ctor_get(v_fst_1883_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v_fst_1883_, 1);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_val_1888_);
v___x_1890_ = v___x_1881_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1878_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1878_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_ctx_1847_);
v_a_1902_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1864_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1864_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1847_ = stack[0].m_obj;
uint8_t v_a_1848_ = stack[1].m_num;
lean_object* v_t_1849_ = stack[2].m_obj;
lean_object* v_init_1850_ = stack[3].m_obj;
lean_object* v___y_1851_ = stack[4].m_obj;
lean_object* v___y_1852_ = stack[5].m_obj;
lean_object* v___y_1853_ = stack[6].m_obj;
lean_object* v___y_1854_ = stack[7].m_obj;
lean_object* v___y_1855_ = stack[8].m_obj;
lean_object* v___y_1856_ = stack[9].m_obj;
lean_object* v___y_1857_ = stack[10].m_obj;
lean_object* v___y_1858_ = stack[11].m_obj;
lean_object* v___y_1859_ = stack[12].m_obj;
lean_object* v___y_1860_ = stack[13].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1847_, v_a_1848_, v_t_1849_, v_init_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1911_, lean_object* v_a_1912_, lean_object* v_t_1913_, lean_object* v_init_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
uint8_t v_a_164779__boxed_1926_; lean_object* v_res_1927_; 
v_a_164779__boxed_1926_ = lean_unbox(v_a_1912_);
v_res_1927_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1911_, v_a_164779__boxed_1926_, v_t_1913_, v_init_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v_t_1913_);
return v_res_1927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1933_ = l_Lean_Name_append(v___x_1932_, v___x_1931_);
return v___x_1933_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1934_, size_t v_i_1935_, size_t v_stop_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_a_1950_; uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_eq(v_i_1935_, v_stop_1936_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_array_uget_borrowed(v_as_1934_, v_i_1935_);
v___x_1956_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1955_, v___y_1938_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1958_ == 0)
{
if (lean_obj_tag(v___x_1955_) == 2)
{
lean_object* v_a_1959_; lean_object* v_b_1960_; lean_object* v_eq_1961_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_toCold_2017_; lean_object* v_options_2018_; uint8_t v_hasTrace_2019_; 
v_a_1959_ = lean_ctor_get(v___x_1955_, 0);
v_b_1960_ = lean_ctor_get(v___x_1955_, 1);
v_eq_1961_ = lean_ctor_get(v___x_1955_, 3);
v_toCold_2017_ = lean_ctor_get(v___y_1946_, 0);
v_options_2018_ = lean_ctor_get(v_toCold_2017_, 2);
v_hasTrace_2019_ = lean_ctor_get_uint8(v_options_2018_, sizeof(void*)*1);
if (v_hasTrace_2019_ == 0)
{
v___y_1986_ = v___y_1938_;
v___y_1987_ = v___y_1939_;
v___y_1988_ = v___y_1940_;
v___y_1989_ = v___y_1941_;
v___y_1990_ = v___y_1942_;
v___y_1991_ = v___y_1943_;
v___y_1992_ = v___y_1944_;
v___y_1993_ = v___y_1945_;
v___y_1994_ = v___y_1946_;
v___y_1995_ = v___y_1947_;
goto v___jp_1985_;
}
else
{
lean_object* v_inheritedTraceOptions_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_inheritedTraceOptions_2020_ = lean_ctor_get(v_toCold_2017_, 11);
v___x_2021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_2022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_2023_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2020_, v_options_2018_, v___x_2022_);
if (v___x_2023_ == 0)
{
v___y_1986_ = v___y_1938_;
v___y_1987_ = v___y_1939_;
v___y_1988_ = v___y_1940_;
v___y_1989_ = v___y_1941_;
v___y_1990_ = v___y_1942_;
v___y_1991_ = v___y_1943_;
v___y_1992_ = v___y_1944_;
v___y_1993_ = v___y_1945_;
v___y_1994_ = v___y_1946_;
v___y_1995_ = v___y_1947_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_inc_ref(v_eq_1961_);
v___x_2024_ = l_Lean_MessageData_ofExpr(v_eq_1961_);
v___x_2025_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_2021_, v___x_2024_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_dec_ref_known(v___x_2025_, 1);
v___y_1986_ = v___y_1938_;
v___y_1987_ = v___y_1939_;
v___y_1988_ = v___y_1940_;
v___y_1989_ = v___y_1941_;
v___y_1990_ = v___y_1942_;
v___y_1991_ = v___y_1943_;
v___y_1992_ = v___y_1944_;
v___y_1993_ = v___y_1945_;
v___y_1994_ = v___y_1946_;
v___y_1995_ = v___y_1947_;
goto v___jp_1985_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_b_1937_);
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_box(0);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1970_);
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1967_);
lean_inc(v___y_1971_);
lean_inc_ref(v_eq_1961_);
v___x_1975_ = lean_grind_internalize(v_eq_1961_, v___y_1973_, v___x_1974_, v___y_1971_, v___y_1967_, v___y_1963_, v___y_1968_, v___y_1970_, v___y_1972_, v___y_1966_, v___y_1969_, v___y_1965_, v___y_1964_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; 
lean_dec_ref_known(v___x_1975_, 1);
lean_inc_ref(v___x_1955_);
v___x_1976_ = lean_array_push(v_b_1937_, v___x_1955_);
v_a_1950_ = v___x_1976_;
goto v___jp_1949_;
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_b_1937_);
v_a_1977_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1975_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1975_);
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
v___jp_1985_:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1959_, v___y_1986_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1960_, v___y_1986_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = lean_nat_dec_le(v_a_1997_, v_a_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v_a_1999_);
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1994_;
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1987_;
v___y_1968_ = v___y_1989_;
v___y_1969_ = v___y_1993_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1986_;
v___y_1972_ = v___y_1991_;
v___y_1973_ = v_a_1997_;
goto v___jp_1962_;
}
else
{
lean_dec(v_a_1997_);
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1994_;
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1987_;
v___y_1968_ = v___y_1989_;
v___y_1969_ = v___y_1993_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1986_;
v___y_1972_ = v___y_1991_;
v___y_1973_ = v_a_1999_;
goto v___jp_1962_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1997_);
lean_dec_ref(v_b_1937_);
v_a_2001_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1998_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1998_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_b_1937_);
v_a_2009_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1996_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1996_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
v_a_1950_ = v_b_1937_;
goto v___jp_1949_;
}
}
else
{
v_a_1950_ = v_b_1937_;
goto v___jp_1949_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_b_1937_);
v_a_2034_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1956_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1956_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_b_1937_);
return v___x_2042_;
}
v___jp_1949_:
{
size_t v___x_1951_; size_t v___x_1952_; 
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1935_, v___x_1951_);
v_i_1935_ = v___x_1952_;
v_b_1937_ = v_a_1950_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1934_ = stack[0].m_obj;
size_t v_i_1935_ = stack[1].m_num;
size_t v_stop_1936_ = stack[2].m_num;
lean_object* v_b_1937_ = stack[3].m_obj;
lean_object* v___y_1938_ = stack[4].m_obj;
lean_object* v___y_1939_ = stack[5].m_obj;
lean_object* v___y_1940_ = stack[6].m_obj;
lean_object* v___y_1941_ = stack[7].m_obj;
lean_object* v___y_1942_ = stack[8].m_obj;
lean_object* v___y_1943_ = stack[9].m_obj;
lean_object* v___y_1944_ = stack[10].m_obj;
lean_object* v___y_1945_ = stack[11].m_obj;
lean_object* v___y_1946_ = stack[12].m_obj;
lean_object* v___y_1947_ = stack[13].m_obj;
lean_object* v_res_2043_;
v_res_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_1934_, v_i_1935_, v_stop_1936_, v_b_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
stack->m_obj
 = v_res_2043_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_2044_, lean_object* v_i_2045_, lean_object* v_stop_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_i_boxed_2059_; size_t v_stop_boxed_2060_; lean_object* v_res_2061_; 
v_i_boxed_2059_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_stop_boxed_2060_ = lean_unbox_usize(v_stop_2046_);
lean_dec(v_stop_2046_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2044_, v_i_boxed_2059_, v_stop_boxed_2060_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v_as_2044_);
return v_res_2061_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2064_, lean_object* v_start_2065_, lean_object* v_stop_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2079_ = lean_nat_dec_lt(v_start_2065_, v_stop_2066_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
return v___x_2080_;
}
else
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = lean_array_get_size(v_as_2064_);
v___x_2082_ = lean_nat_dec_le(v_stop_2066_, v___x_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_nat_dec_lt(v_start_2065_, v___x_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2078_);
return v___x_2084_;
}
else
{
size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_usize_of_nat(v_start_2065_);
v___x_2086_ = lean_usize_of_nat(v___x_2081_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2064_, v___x_2085_, v___x_2086_, v___x_2078_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
return v___x_2087_;
}
}
else
{
size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_usize_of_nat(v_start_2065_);
v___x_2089_ = lean_usize_of_nat(v_stop_2066_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2064_, v___x_2088_, v___x_2089_, v___x_2078_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
return v___x_2090_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2064_ = stack[0].m_obj;
lean_object* v_start_2065_ = stack[1].m_obj;
lean_object* v_stop_2066_ = stack[2].m_obj;
lean_object* v___y_2067_ = stack[3].m_obj;
lean_object* v___y_2068_ = stack[4].m_obj;
lean_object* v___y_2069_ = stack[5].m_obj;
lean_object* v___y_2070_ = stack[6].m_obj;
lean_object* v___y_2071_ = stack[7].m_obj;
lean_object* v___y_2072_ = stack[8].m_obj;
lean_object* v___y_2073_ = stack[9].m_obj;
lean_object* v___y_2074_ = stack[10].m_obj;
lean_object* v___y_2075_ = stack[11].m_obj;
lean_object* v___y_2076_ = stack[12].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2064_, v_start_2065_, v_stop_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2092_, lean_object* v_start_2093_, lean_object* v_stop_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2092_, v_start_2093_, v_stop_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v_stop_2094_);
lean_dec(v_start_2093_);
lean_dec_ref(v_as_2092_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_unsigned_to_nat(16u);
v___x_2109_ = lean_mk_array(v___x_2108_, v___x_2107_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2110_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2124_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2335_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2335_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2335_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v_mbtc_2138_; 
v_mbtc_2138_ = lean_ctor_get_uint8(v_a_2134_, sizeof(void*)*14 + 18);
lean_dec(v_a_2134_);
if (v_mbtc_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_dec_ref(v_ctx_2121_);
v___x_2139_ = lean_box(v_mbtc_2138_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2141_ = v___x_2136_;
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
else
{
lean_object* v___x_2143_; 
lean_del_object(v___x_2136_);
v___x_2143_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2122_, v_a_2124_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2334_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2334_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2334_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_unbox(v_a_2144_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_toGoalState_2151_; lean_object* v_exprs_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; 
lean_del_object(v___x_2146_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_st_ref_get(v_a_2122_);
v_toGoalState_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_ref(v_toGoalState_2151_);
lean_dec(v___x_2150_);
v_exprs_2152_ = lean_ctor_get(v_toGoalState_2151_, 2);
lean_inc_ref(v_exprs_2152_);
lean_dec_ref(v_toGoalState_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2154_ = lean_unbox(v_a_2144_);
v___x_2155_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2121_, v___x_2154_, v_exprs_2152_, v___x_2153_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_exprs_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2320_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2320_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2320_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_snd_2160_; lean_object* v_size_2161_; lean_object* v_buckets_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2319_; 
v_snd_2160_ = lean_ctor_get(v_a_2156_, 1);
lean_inc(v_snd_2160_);
lean_dec(v_a_2156_);
v_size_2161_ = lean_ctor_get(v_snd_2160_, 0);
v_buckets_2162_ = lean_ctor_get(v_snd_2160_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_snd_2160_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2164_ = v_snd_2160_;
v_isShared_2165_ = v_isSharedCheck_2319_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_buckets_2162_);
lean_inc(v_size_2161_);
lean_dec(v_snd_2160_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2319_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_nat_dec_eq(v_size_2161_, v___x_2149_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2144_);
v___x_2167_ = lean_st_ref_get(v_a_2122_);
v___x_2168_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2124_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v_toGoalState_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2306_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v_toGoalState_2170_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2167_, 1);
lean_dec(v_unused_2307_);
v___x_2172_ = v___x_2167_;
v_isShared_2173_ = v_isSharedCheck_2306_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_toGoalState_2170_);
lean_dec(v___x_2167_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2306_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_split_2174_; lean_object* v_splits_2175_; lean_object* v_num_2176_; uint8_t v___x_2177_; lean_object* v___y_2179_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2235_; 
v_split_2174_ = lean_ctor_get(v_toGoalState_2170_, 14);
lean_inc_ref(v_split_2174_);
lean_dec_ref(v_toGoalState_2170_);
v_splits_2175_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_splits_2175_);
lean_dec(v_a_2169_);
v_num_2176_ = lean_ctor_get(v_split_2174_, 0);
lean_inc(v_num_2176_);
lean_dec_ref(v_split_2174_);
v___x_2177_ = lean_nat_dec_lt(v_splits_2175_, v_num_2176_);
lean_dec(v_num_2176_);
lean_dec(v_splits_2175_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
lean_del_object(v___x_2172_);
lean_del_object(v___x_2164_);
v___x_2241_ = lean_mk_empty_array_with_capacity(v_size_2161_);
lean_dec(v_size_2161_);
v___x_2242_ = lean_array_get_size(v_buckets_2162_);
v___x_2243_ = lean_nat_dec_lt(v___x_2149_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_dec_ref(v_buckets_2162_);
v___y_2235_ = v___x_2241_;
goto v___jp_2234_;
}
else
{
size_t v___x_2244_; size_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = lean_usize_of_nat(v___x_2242_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2162_, v___x_2244_, v___x_2245_, v___x_2241_);
lean_dec_ref(v_buckets_2162_);
v___y_2235_ = v___x_2246_;
goto v___jp_2234_;
}
}
else
{
lean_object* v___x_2247_; 
lean_dec_ref(v_buckets_2162_);
lean_dec(v_size_2161_);
v___x_2247_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2124_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v_splits_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v_splits_2249_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_splits_2249_);
lean_dec(v_a_2248_);
v___x_2250_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2251_ = l_Nat_reprFast(v_splits_2249_);
v___x_2252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
v___x_2253_ = l_Lean_MessageData_ofFormat(v___x_2252_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 7);
lean_ctor_set(v___x_2172_, 1, v___x_2253_);
lean_ctor_set(v___x_2172_, 0, v___x_2250_);
v___x_2255_ = v___x_2172_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 7);
lean_ctor_set(v___x_2164_, 1, v___x_2256_);
lean_ctor_set(v___x_2164_, 0, v___x_2255_);
v___x_2258_ = v___x_2164_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2126_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2287_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2287_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2287_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint8_t v_verbose_2264_; 
v_verbose_2264_ = lean_ctor_get_uint8(v_a_2260_, 0);
lean_dec(v_a_2260_);
if (v_verbose_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec_ref(v___x_2258_);
v___x_2265_ = lean_box(v___x_2166_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2265_);
v___x_2267_ = v___x_2262_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
else
{
lean_object* v___x_2269_; 
lean_del_object(v___x_2262_);
v___x_2269_ = l_Lean_Meta_Sym_reportIssue(v___x_2258_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2277_; 
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v___x_2269_, 0);
lean_dec(v_unused_2278_);
v___x_2271_ = v___x_2269_;
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
else
{
lean_dec(v___x_2269_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(v___x_2166_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_a_2279_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2269_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v___x_2258_);
v_a_2288_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2259_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2259_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2172_);
lean_del_object(v___x_2164_);
v_a_2298_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2247_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2247_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
v___jp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_array_get_size(v___y_2179_);
v___x_2181_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2179_, v___x_2149_, v___x_2180_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec_ref(v___y_2179_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2213_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2213_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2213_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_array_get_size(v_a_2182_);
v___x_2187_ = lean_nat_dec_eq(v___x_2186_, v___x_2149_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
lean_del_object(v___x_2184_);
v___x_2188_ = lean_box(0);
v_sz_2189_ = lean_array_size(v_a_2182_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2182_, v_sz_2189_, v___x_2190_, v___x_2188_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2182_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2191_, 0);
lean_dec(v_unused_2200_);
v___x_2193_ = v___x_2191_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v___x_2191_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_box(v_mbtc_2138_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
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
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2201_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2191_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2191_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_dec(v_a_2182_);
v___x_2209_ = lean_box(v___x_2177_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2209_);
v___x_2211_ = v___x_2184_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2181_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2181_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
v___jp_2222_:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2224_, v___y_2223_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec(v___y_2224_);
v___y_2179_ = v___x_2227_;
goto v___jp_2178_;
}
v___jp_2228_:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_nat_dec_le(v___y_2232_, v___y_2231_);
if (v___x_2233_ == 0)
{
lean_dec(v___y_2231_);
lean_inc(v___y_2232_);
v___y_2223_ = v___y_2229_;
v___y_2224_ = v___y_2230_;
v___y_2225_ = v___y_2232_;
v___y_2226_ = v___y_2232_;
goto v___jp_2222_;
}
else
{
v___y_2223_ = v___y_2229_;
v___y_2224_ = v___y_2230_;
v___y_2225_ = v___y_2232_;
v___y_2226_ = v___y_2231_;
goto v___jp_2222_;
}
}
v___jp_2234_:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = lean_array_get_size(v___y_2235_);
v___x_2237_ = lean_nat_dec_eq(v___x_2236_, v___x_2149_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_sub(v___x_2236_, v___x_2238_);
v___x_2240_ = lean_nat_dec_le(v___x_2149_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_inc(v___x_2239_);
v___y_2229_ = v___y_2235_;
v___y_2230_ = v___x_2236_;
v___y_2231_ = v___x_2239_;
v___y_2232_ = v___x_2239_;
goto v___jp_2228_;
}
else
{
v___y_2229_ = v___y_2235_;
v___y_2230_ = v___x_2236_;
v___y_2231_ = v___x_2239_;
v___y_2232_ = v___x_2149_;
goto v___jp_2228_;
}
}
else
{
v___y_2179_ = v___y_2235_;
goto v___jp_2178_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v___x_2167_);
lean_del_object(v___x_2164_);
lean_dec_ref(v_buckets_2162_);
lean_dec(v_size_2161_);
v_a_2308_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2168_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2168_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v___x_2317_; 
lean_del_object(v___x_2164_);
lean_dec_ref(v_buckets_2162_);
lean_dec(v_size_2161_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v_a_2144_);
v___x_2317_ = v___x_2158_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2144_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2144_);
v_a_2321_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2155_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2155_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec(v_a_2144_);
lean_dec_ref(v_ctx_2121_);
v___x_2329_ = 0;
v___x_2330_ = lean_box(v___x_2329_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2330_);
v___x_2332_ = v___x_2146_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2121_);
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_ctx_2121_);
v_a_2336_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2133_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2133_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mbtc_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2121_ = stack[0].m_obj;
lean_object* v_a_2122_ = stack[1].m_obj;
lean_object* v_a_2123_ = stack[2].m_obj;
lean_object* v_a_2124_ = stack[3].m_obj;
lean_object* v_a_2125_ = stack[4].m_obj;
lean_object* v_a_2126_ = stack[5].m_obj;
lean_object* v_a_2127_ = stack[6].m_obj;
lean_object* v_a_2128_ = stack[7].m_obj;
lean_object* v_a_2129_ = stack[8].m_obj;
lean_object* v_a_2130_ = stack[9].m_obj;
lean_object* v_a_2131_ = stack[10].m_obj;
lean_object* v_res_2344_;
v_res_2344_ = l_Lean_Meta_Grind_mbtc(v_ctx_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
stack->m_obj
 = v_res_2344_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Meta_Grind_mbtc(v_ctx_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec(v_a_2346_);
return v_res_2357_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2358_, v_msg_2359_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2358_ = stack[0].m_obj;
lean_object* v_msg_2359_ = stack[1].m_obj;
lean_object* v___y_2360_ = stack[2].m_obj;
lean_object* v___y_2361_ = stack[3].m_obj;
lean_object* v___y_2362_ = stack[4].m_obj;
lean_object* v___y_2363_ = stack[5].m_obj;
lean_object* v___y_2364_ = stack[6].m_obj;
lean_object* v___y_2365_ = stack[7].m_obj;
lean_object* v___y_2366_ = stack[8].m_obj;
lean_object* v___y_2367_ = stack[9].m_obj;
lean_object* v___y_2368_ = stack[10].m_obj;
lean_object* v___y_2369_ = stack[11].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2358_, v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
stack->m_obj
 = v_res_2372_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2373_, lean_object* v_msg_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2373_, v_msg_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2387_, lean_object* v_m_2388_, lean_object* v_a_2389_, lean_object* v_b_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2388_, v_a_2389_, v_b_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2392_, lean_object* v_m_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2393_, v_a_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2396_, lean_object* v_m_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2396_, v_m_2397_, v_a_2398_);
lean_dec_ref(v_a_2398_);
lean_dec_ref(v_m_2397_);
return v_res_2399_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2400_, lean_object* v_val_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v_as_2404_, lean_object* v_as_x27_2405_, lean_object* v_b_2406_, lean_object* v_a_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2400_, v_val_2401_, v___x_2402_, v___x_2403_, v_as_x27_2405_, v_b_2406_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2400_ = stack[0].m_obj;
lean_object* v_val_2401_ = stack[1].m_obj;
lean_object* v___x_2402_ = stack[2].m_obj;
lean_object* v___x_2403_ = stack[3].m_obj;
lean_object* v_as_2404_ = stack[4].m_obj;
lean_object* v_as_x27_2405_ = stack[5].m_obj;
lean_object* v_b_2406_ = stack[6].m_obj;
lean_object* v___y_2408_ = stack[8].m_obj;
lean_object* v___y_2409_ = stack[9].m_obj;
lean_object* v___y_2410_ = stack[10].m_obj;
lean_object* v___y_2411_ = stack[11].m_obj;
lean_object* v___y_2412_ = stack[12].m_obj;
lean_object* v___y_2413_ = stack[13].m_obj;
lean_object* v___y_2414_ = stack[14].m_obj;
lean_object* v___y_2415_ = stack[15].m_obj;
lean_object* v___y_2416_ = stack[16].m_obj;
lean_object* v___y_2417_ = stack[17].m_obj;
lean_object* v_res_2420_;
v_res_2420_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2400_, v_val_2401_, v___x_2402_, v___x_2403_, v_as_2404_, v_as_x27_2405_, v_b_2406_, lean_box(0), v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2421_ = _args[0];
lean_object* v_val_2422_ = _args[1];
lean_object* v___x_2423_ = _args[2];
lean_object* v___x_2424_ = _args[3];
lean_object* v_as_2425_ = _args[4];
lean_object* v_as_x27_2426_ = _args[5];
lean_object* v_b_2427_ = _args[6];
lean_object* v_a_2428_ = _args[7];
lean_object* v___y_2429_ = _args[8];
lean_object* v___y_2430_ = _args[9];
lean_object* v___y_2431_ = _args[10];
lean_object* v___y_2432_ = _args[11];
lean_object* v___y_2433_ = _args[12];
lean_object* v___y_2434_ = _args[13];
lean_object* v___y_2435_ = _args[14];
lean_object* v___y_2436_ = _args[15];
lean_object* v___y_2437_ = _args[16];
lean_object* v___y_2438_ = _args[17];
lean_object* v___y_2439_ = _args[18];
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2421_, v_val_2422_, v___x_2423_, v___x_2424_, v_as_2425_, v_as_x27_2426_, v_b_2427_, v_a_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec(v_as_x27_2426_);
lean_dec(v_as_2425_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2441_, lean_object* v_m_2442_, lean_object* v_a_2443_, lean_object* v_b_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2442_, v_a_2443_, v_b_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2446_, lean_object* v_as_2447_, lean_object* v_lo_2448_, lean_object* v_hi_2449_, lean_object* v_w_2450_, lean_object* v_hlo_2451_, lean_object* v_hhi_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2446_, v_as_2447_, v_lo_2448_, v_hi_2449_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2454_, lean_object* v_as_2455_, lean_object* v_lo_2456_, lean_object* v_hi_2457_, lean_object* v_w_2458_, lean_object* v_hlo_2459_, lean_object* v_hhi_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2454_, v_as_2455_, v_lo_2456_, v_hi_2457_, v_w_2458_, v_hlo_2459_, v_hhi_2460_);
lean_dec(v_hi_2457_);
lean_dec(v_n_2454_);
return v_res_2461_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2462_, lean_object* v_a_2463_, lean_object* v_x_2464_){
_start:
{
uint8_t v___x_2465_; 
v___x_2465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2463_ = stack[1].m_obj;
lean_object* v_x_2464_ = stack[2].m_obj;
uint8_t v_res_2466_;
v_res_2466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_box(0), v_a_2463_, v_x_2464_);
stack->m_num = v_res_2466_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2467_, lean_object* v_a_2468_, lean_object* v_x_2469_){
_start:
{
uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_res_2470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2467_, v_a_2468_, v_x_2469_);
lean_dec(v_x_2469_);
lean_dec_ref(v_a_2468_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2472_, lean_object* v_data_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2475_, lean_object* v_a_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2476_, v_x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2479_, lean_object* v_a_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2479_, v_a_2480_, v_x_2481_);
lean_dec(v_x_2481_);
lean_dec_ref(v_a_2480_);
return v_res_2482_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2483_, lean_object* v_a_2484_, lean_object* v_x_2485_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2484_, v_x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2484_ = stack[1].m_obj;
lean_object* v_x_2485_ = stack[2].m_obj;
uint8_t v_res_2487_;
v_res_2487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_box(0), v_a_2484_, v_x_2485_);
stack->m_num = v_res_2487_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2488_, lean_object* v_a_2489_, lean_object* v_x_2490_){
_start:
{
uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_res_2491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2488_, v_a_2489_, v_x_2490_);
lean_dec(v_x_2490_);
lean_dec_ref(v_a_2489_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2493_, lean_object* v_data_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2496_, lean_object* v_a_2497_, lean_object* v_b_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2497_, v_b_2498_, v_x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2501_, lean_object* v_lo_2502_, lean_object* v_hi_2503_, lean_object* v_hhi_2504_, lean_object* v_pivot_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_k_2508_, lean_object* v_ilo_2509_, lean_object* v_ik_2510_, lean_object* v_w_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2503_, v_pivot_2505_, v_as_2506_, v_i_2507_, v_k_2508_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2513_, lean_object* v_lo_2514_, lean_object* v_hi_2515_, lean_object* v_hhi_2516_, lean_object* v_pivot_2517_, lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_k_2520_, lean_object* v_ilo_2521_, lean_object* v_ik_2522_, lean_object* v_w_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2513_, v_lo_2514_, v_hi_2515_, v_hhi_2516_, v_pivot_2517_, v_as_2518_, v_i_2519_, v_k_2520_, v_ilo_2521_, v_ik_2522_, v_w_2523_);
lean_dec_ref(v_pivot_2517_);
lean_dec(v_hi_2515_);
lean_dec(v_lo_2514_);
lean_dec(v_n_2513_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2525_, lean_object* v_i_2526_, lean_object* v_source_2527_, lean_object* v_target_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2526_, v_source_2527_, v_target_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2530_, lean_object* v_i_2531_, lean_object* v_source_2532_, lean_object* v_target_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2531_, v_source_2532_, v_target_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2536_, v_x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2540_, v_x_2541_);
return v___x_2542_;
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
