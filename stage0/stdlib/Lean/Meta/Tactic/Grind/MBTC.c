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
lean_object* v___x_489_; lean_object* v_env_490_; uint8_t v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_toCold_494_; lean_object* v_mctx_495_; lean_object* v_lctx_496_; lean_object* v_options_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_489_ = lean_st_ref_get(v___y_487_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_env_490_);
lean_dec(v___x_489_);
v___x_491_ = 0;
v_env_492_ = l_Lean_Environment_setRecordingDeps(v_env_490_, v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_485_);
v_toCold_494_ = lean_ctor_get(v___y_486_, 0);
v_mctx_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_495_);
lean_dec(v___x_493_);
v_lctx_496_ = lean_ctor_get(v___y_484_, 2);
v_options_497_ = lean_ctor_get(v_toCold_494_, 2);
lean_inc_ref(v_options_497_);
lean_inc_ref(v_lctx_496_);
v___x_498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_498_, 0, v_env_492_);
lean_ctor_set(v___x_498_, 1, v_mctx_495_);
lean_ctor_set(v___x_498_, 2, v_lctx_496_);
lean_ctor_set(v___x_498_, 3, v_options_497_);
v___x_499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_msgData_483_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object* v_msgData_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_508_; double v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_float_of_nat(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* v_cls_513_, lean_object* v_msg_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_ref_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_567_; 
v_ref_520_ = lean_ctor_get(v___y_517_, 2);
v___x_521_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_567_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_567_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_567_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v_traceState_527_; lean_object* v_env_528_; lean_object* v_nextMacroScope_529_; lean_object* v_ngen_530_; lean_object* v_auxDeclNGen_531_; lean_object* v_cache_532_; lean_object* v_recordedDeps_533_; lean_object* v_messages_534_; lean_object* v_infoState_535_; lean_object* v_snapshotTasks_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_566_; 
v___x_526_ = lean_st_ref_take(v___y_518_);
v_traceState_527_ = lean_ctor_get(v___x_526_, 4);
v_env_528_ = lean_ctor_get(v___x_526_, 0);
v_nextMacroScope_529_ = lean_ctor_get(v___x_526_, 1);
v_ngen_530_ = lean_ctor_get(v___x_526_, 2);
v_auxDeclNGen_531_ = lean_ctor_get(v___x_526_, 3);
v_cache_532_ = lean_ctor_get(v___x_526_, 5);
v_recordedDeps_533_ = lean_ctor_get(v___x_526_, 6);
v_messages_534_ = lean_ctor_get(v___x_526_, 7);
v_infoState_535_ = lean_ctor_get(v___x_526_, 8);
v_snapshotTasks_536_ = lean_ctor_get(v___x_526_, 9);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_566_ == 0)
{
v___x_538_ = v___x_526_;
v_isShared_539_ = v_isSharedCheck_566_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snapshotTasks_536_);
lean_inc(v_infoState_535_);
lean_inc(v_messages_534_);
lean_inc(v_recordedDeps_533_);
lean_inc(v_cache_532_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_531_);
lean_inc(v_ngen_530_);
lean_inc(v_nextMacroScope_529_);
lean_inc(v_env_528_);
lean_dec(v___x_526_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_566_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint64_t v_tid_540_; lean_object* v_traces_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_565_; 
v_tid_540_ = lean_ctor_get_uint64(v_traceState_527_, sizeof(void*)*1);
v_traces_541_ = lean_ctor_get(v_traceState_527_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_traceState_527_);
if (v_isSharedCheck_565_ == 0)
{
v___x_543_ = v_traceState_527_;
v_isShared_544_ = v_isSharedCheck_565_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_traces_541_);
lean_dec(v_traceState_527_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_565_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; double v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_545_ = lean_box(0);
v___x_546_ = lean_box(0);
v___x_547_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_548_ = 0;
v___x_549_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_550_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_550_, 0, v_cls_513_);
lean_ctor_set(v___x_550_, 1, v___x_546_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set_float(v___x_550_, sizeof(void*)*3, v___x_547_);
lean_ctor_set_float(v___x_550_, sizeof(void*)*3 + 8, v___x_547_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*3 + 16, v___x_548_);
v___x_551_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_552_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v_a_522_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
lean_inc(v_ref_520_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_ref_520_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_PersistentArray_push___redArg(v_traces_541_, v___x_553_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_554_);
v___x_556_ = v___x_543_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_554_);
lean_ctor_set_uint64(v_reuseFailAlloc_564_, sizeof(void*)*1, v_tid_540_);
v___x_556_ = v_reuseFailAlloc_564_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_556_);
v___x_558_ = v___x_538_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_env_528_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_nextMacroScope_529_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_ngen_530_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_auxDeclNGen_531_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_cache_532_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_recordedDeps_533_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_messages_534_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_infoState_535_);
lean_ctor_set(v_reuseFailAlloc_563_, 9, v_snapshotTasks_536_);
v___x_558_ = v_reuseFailAlloc_563_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_st_ref_put(v___y_518_, v___x_558_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_545_);
v___x_561_ = v___x_524_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_545_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_568_, lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_568_, v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
uint8_t v___x_578_; 
v___x_578_ = 0;
return v___x_578_;
}
else
{
lean_object* v_key_579_; lean_object* v_tail_580_; uint8_t v___x_581_; 
v_key_579_ = lean_ctor_get(v_x_577_, 0);
v_tail_580_ = lean_ctor_get(v_x_577_, 2);
v___x_581_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_579_, v_a_576_);
if (v___x_581_ == 0)
{
v_x_577_ = v_tail_580_;
goto _start;
}
else
{
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_583_, v_x_584_);
lean_dec(v_x_584_);
lean_dec_ref(v_a_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
return v_x_587_;
}
else
{
lean_object* v_key_589_; lean_object* v_value_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_key_589_ = lean_ctor_get(v_x_588_, 0);
v_value_590_ = lean_ctor_get(v_x_588_, 1);
v_tail_591_ = lean_ctor_get(v_x_588_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v_x_588_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_value_590_);
lean_inc(v_key_589_);
lean_dec(v_x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v_fold_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_595_ = lean_array_get_size(v_x_587_);
v___x_596_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_589_);
v___x_597_ = 32ULL;
v___x_598_ = lean_uint64_shift_right(v___x_596_, v___x_597_);
v_fold_599_ = lean_uint64_xor(v___x_596_, v___x_598_);
v___x_600_ = 16ULL;
v___x_601_ = lean_uint64_shift_right(v_fold_599_, v___x_600_);
v___x_602_ = lean_uint64_xor(v_fold_599_, v___x_601_);
v___x_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = lean_usize_of_nat(v___x_595_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_sub(v___x_604_, v___x_605_);
v___x_607_ = lean_usize_land(v___x_603_, v___x_606_);
v___x_608_ = lean_array_uget_borrowed(v_x_587_, v___x_607_);
lean_inc(v___x_608_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v___x_608_);
v___x_610_ = v___x_593_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_key_589_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_value_590_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___x_608_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = lean_array_uset(v_x_587_, v___x_607_, v___x_610_);
v_x_587_ = v___x_611_;
v_x_588_ = v_tail_591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object* v_i_615_, lean_object* v_source_616_, lean_object* v_target_617_){
_start:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_array_get_size(v_source_616_);
v___x_619_ = lean_nat_dec_lt(v_i_615_, v___x_618_);
if (v___x_619_ == 0)
{
lean_dec_ref(v_source_616_);
lean_dec(v_i_615_);
return v_target_617_;
}
else
{
lean_object* v_es_620_; lean_object* v___x_621_; lean_object* v_source_622_; lean_object* v_target_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_es_620_ = lean_array_fget(v_source_616_, v_i_615_);
v___x_621_ = lean_box(0);
v_source_622_ = lean_array_fset(v_source_616_, v_i_615_, v___x_621_);
v_target_623_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_617_, v_es_620_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_i_615_, v___x_624_);
lean_dec(v_i_615_);
v_i_615_ = v___x_625_;
v_source_616_ = v_source_622_;
v_target_617_ = v_target_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object* v_data_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_nbuckets_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_628_ = lean_array_get_size(v_data_627_);
v___x_629_ = lean_unsigned_to_nat(2u);
v_nbuckets_630_ = lean_nat_mul(v___x_628_, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_box(0);
v___x_633_ = lean_mk_array(v_nbuckets_630_, v___x_632_);
v___x_634_ = lean_array_propagate_mark(v_data_627_, v___x_633_);
v___x_635_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_631_, v_data_627_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_636_, lean_object* v_a_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_size_639_; lean_object* v_buckets_640_; lean_object* v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v_fold_645_; uint64_t v___x_646_; uint64_t v___x_647_; uint64_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; lean_object* v_bkt_654_; uint8_t v___x_655_; 
v_size_639_ = lean_ctor_get(v_m_636_, 0);
v_buckets_640_ = lean_ctor_get(v_m_636_, 1);
v___x_641_ = lean_array_get_size(v_buckets_640_);
v___x_642_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_637_);
v___x_643_ = 32ULL;
v___x_644_ = lean_uint64_shift_right(v___x_642_, v___x_643_);
v_fold_645_ = lean_uint64_xor(v___x_642_, v___x_644_);
v___x_646_ = 16ULL;
v___x_647_ = lean_uint64_shift_right(v_fold_645_, v___x_646_);
v___x_648_ = lean_uint64_xor(v_fold_645_, v___x_647_);
v___x_649_ = lean_uint64_to_usize(v___x_648_);
v___x_650_ = lean_usize_of_nat(v___x_641_);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_sub(v___x_650_, v___x_651_);
v___x_653_ = lean_usize_land(v___x_649_, v___x_652_);
v_bkt_654_ = lean_array_uget_borrowed(v_buckets_640_, v___x_653_);
v___x_655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_637_, v_bkt_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_676_; 
lean_inc_ref(v_buckets_640_);
lean_inc(v_size_639_);
v_isSharedCheck_676_ = !lean_is_exclusive(v_m_636_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v_m_636_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_m_636_, 0);
lean_dec(v_unused_678_);
v___x_657_ = v_m_636_;
v_isShared_658_ = v_isSharedCheck_676_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_m_636_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_676_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v_size_x27_660_; lean_object* v___x_661_; lean_object* v_buckets_x27_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v_size_x27_660_ = lean_nat_add(v_size_639_, v___x_659_);
lean_dec(v_size_639_);
lean_inc(v_bkt_654_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v_a_637_);
lean_ctor_set(v___x_661_, 1, v_b_638_);
lean_ctor_set(v___x_661_, 2, v_bkt_654_);
v_buckets_x27_662_ = lean_array_uset(v_buckets_640_, v___x_653_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v_size_x27_660_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_div(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_array_get_size(v_buckets_x27_662_);
v___x_668_ = lean_nat_dec_le(v___x_666_, v___x_667_);
lean_dec(v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_662_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_val_669_);
lean_ctor_set(v___x_657_, 0, v_size_x27_660_);
v___x_671_ = v___x_657_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_val_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_buckets_x27_662_);
lean_ctor_set(v___x_657_, 0, v_size_x27_660_);
v___x_674_ = v___x_657_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_buckets_x27_662_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_dec(v_b_638_);
lean_dec_ref(v_a_637_);
return v_m_636_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_ctx_679_, lean_object* v_val_680_, lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v_as_x27_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
if (lean_obj_tag(v_as_x27_683_) == 0)
{
lean_object* v___x_696_; 
lean_dec(v___x_682_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v_val_680_);
lean_dec_ref(v_ctx_679_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_b_684_);
return v___x_696_;
}
else
{
lean_object* v_head_697_; lean_object* v_tail_698_; lean_object* v_eqAssignment_699_; lean_object* v_arg_700_; lean_object* v___x_701_; 
v_head_697_ = lean_ctor_get(v_as_x27_683_, 0);
v_tail_698_ = lean_ctor_get(v_as_x27_683_, 1);
v_eqAssignment_699_ = lean_ctor_get(v_ctx_679_, 2);
v_arg_700_ = lean_ctor_get(v_head_697_, 0);
lean_inc_ref(v_eqAssignment_699_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc(v___y_685_);
lean_inc_ref(v_arg_700_);
lean_inc_ref(v_val_680_);
v___x_701_ = lean_apply_13(v_eqAssignment_699_, v_val_680_, v_arg_700_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, lean_box(0));
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
v_as_x27_683_ = v_tail_698_;
goto _start;
}
else
{
lean_object* v___x_705_; 
lean_inc_ref(v_arg_700_);
lean_inc_ref(v_val_680_);
v___x_705_ = l_Lean_Meta_Grind_hasSameType(v_val_680_, v_arg_700_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; uint8_t v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
if (v___x_707_ == 0)
{
v_as_x27_683_ = v_tail_698_;
goto _start;
}
else
{
lean_object* v___x_709_; 
lean_inc(v___x_682_);
lean_inc(v_head_697_);
lean_inc_ref(v___x_681_);
v___x_709_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_681_, v_head_697_, v___x_682_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_box(0);
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_684_, v_a_710_, v___x_711_);
v_as_x27_683_ = v_tail_698_;
v_b_684_ = v___x_712_;
goto _start;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_b_684_);
lean_dec(v___x_682_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v_val_680_);
lean_dec_ref(v_ctx_679_);
v_a_714_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_709_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_709_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_b_684_);
lean_dec(v___x_682_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v_val_680_);
lean_dec_ref(v_ctx_679_);
v_a_722_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_705_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_705_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_b_684_);
lean_dec(v___x_682_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v_val_680_);
lean_dec_ref(v_ctx_679_);
v_a_730_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_701_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_701_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_ctx_738_ = _args[0];
lean_object* v_val_739_ = _args[1];
lean_object* v___x_740_ = _args[2];
lean_object* v___x_741_ = _args[3];
lean_object* v_as_x27_742_ = _args[4];
lean_object* v_b_743_ = _args[5];
lean_object* v___y_744_ = _args[6];
lean_object* v___y_745_ = _args[7];
lean_object* v___y_746_ = _args[8];
lean_object* v___y_747_ = _args[9];
lean_object* v___y_748_ = _args[10];
lean_object* v___y_749_ = _args[11];
lean_object* v___y_750_ = _args[12];
lean_object* v___y_751_ = _args[13];
lean_object* v___y_752_ = _args[14];
lean_object* v___y_753_ = _args[15];
lean_object* v___y_754_ = _args[16];
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_738_, v_val_739_, v___x_740_, v___x_741_, v_as_x27_742_, v_b_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v_as_x27_742_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(lean_object* v_a_756_, lean_object* v_b_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_dec(v_b_757_);
lean_dec_ref(v_a_756_);
return v_x_758_;
}
else
{
lean_object* v_key_759_; lean_object* v_value_760_; lean_object* v_tail_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v_key_759_ = lean_ctor_get(v_x_758_, 0);
v_value_760_ = lean_ctor_get(v_x_758_, 1);
v_tail_761_ = lean_ctor_get(v_x_758_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v_x_758_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_tail_761_);
lean_inc(v_value_760_);
lean_inc(v_key_759_);
lean_dec(v_x_758_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = lean_expr_eqv(v_key_759_, v_a_756_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_756_, v_b_757_, v_tail_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_key_759_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_value_760_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v___x_771_; 
lean_dec(v_value_760_);
lean_dec(v_key_759_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v_b_757_);
lean_ctor_set(v___x_763_, 0, v_a_756_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_b_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_tail_761_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(lean_object* v_a_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
else
{
lean_object* v_key_777_; lean_object* v_tail_778_; uint8_t v___x_779_; 
v_key_777_ = lean_ctor_get(v_x_775_, 0);
v_tail_778_ = lean_ctor_get(v_x_775_, 2);
v___x_779_ = lean_expr_eqv(v_key_777_, v_a_774_);
if (v___x_779_ == 0)
{
v_x_775_ = v_tail_778_;
goto _start;
}
else
{
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(lean_object* v_a_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec_ref(v_a_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
return v_x_785_;
}
else
{
lean_object* v_key_787_; lean_object* v_value_788_; lean_object* v_tail_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_812_; 
v_key_787_ = lean_ctor_get(v_x_786_, 0);
v_value_788_ = lean_ctor_get(v_x_786_, 1);
v_tail_789_ = lean_ctor_get(v_x_786_, 2);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_812_ == 0)
{
v___x_791_ = v_x_786_;
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_tail_789_);
lean_inc(v_value_788_);
lean_inc(v_key_787_);
lean_dec(v_x_786_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_793_ = lean_array_get_size(v_x_785_);
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_787_);
v___x_795_ = 32ULL;
v___x_796_ = lean_uint64_shift_right(v___x_794_, v___x_795_);
v_fold_797_ = lean_uint64_xor(v___x_794_, v___x_796_);
v___x_798_ = 16ULL;
v___x_799_ = lean_uint64_shift_right(v_fold_797_, v___x_798_);
v___x_800_ = lean_uint64_xor(v_fold_797_, v___x_799_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = lean_usize_of_nat(v___x_793_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_sub(v___x_802_, v___x_803_);
v___x_805_ = lean_usize_land(v___x_801_, v___x_804_);
v___x_806_ = lean_array_uget_borrowed(v_x_785_, v___x_805_);
lean_inc(v___x_806_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 2, v___x_806_);
v___x_808_ = v___x_791_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_key_787_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_value_788_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___x_806_);
v___x_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_array_uset(v_x_785_, v___x_805_, v___x_808_);
v_x_785_ = v___x_809_;
v_x_786_ = v_tail_789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(lean_object* v_i_813_, lean_object* v_source_814_, lean_object* v_target_815_){
_start:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_array_get_size(v_source_814_);
v___x_817_ = lean_nat_dec_lt(v_i_813_, v___x_816_);
if (v___x_817_ == 0)
{
lean_dec_ref(v_source_814_);
lean_dec(v_i_813_);
return v_target_815_;
}
else
{
lean_object* v_es_818_; lean_object* v___x_819_; lean_object* v_source_820_; lean_object* v_target_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_es_818_ = lean_array_fget(v_source_814_, v_i_813_);
v___x_819_ = lean_box(0);
v_source_820_ = lean_array_fset(v_source_814_, v_i_813_, v___x_819_);
v_target_821_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_815_, v_es_818_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_add(v_i_813_, v___x_822_);
lean_dec(v_i_813_);
v_i_813_ = v___x_823_;
v_source_814_ = v_source_820_;
v_target_815_ = v_target_821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(lean_object* v_data_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_nbuckets_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_826_ = lean_array_get_size(v_data_825_);
v___x_827_ = lean_unsigned_to_nat(2u);
v_nbuckets_828_ = lean_nat_mul(v___x_826_, v___x_827_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_box(0);
v___x_831_ = lean_mk_array(v_nbuckets_828_, v___x_830_);
v___x_832_ = lean_array_propagate_mark(v_data_825_, v___x_831_);
v___x_833_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_829_, v_data_825_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_m_834_, lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
lean_object* v_size_837_; lean_object* v_buckets_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_881_; 
v_size_837_ = lean_ctor_get(v_m_834_, 0);
v_buckets_838_ = lean_ctor_get(v_m_834_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_m_834_);
if (v_isSharedCheck_881_ == 0)
{
v___x_840_ = v_m_834_;
v_isShared_841_ = v_isSharedCheck_881_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_buckets_838_);
lean_inc(v_size_837_);
lean_dec(v_m_834_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_881_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v_fold_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v_bkt_855_; uint8_t v___x_856_; 
v___x_842_ = lean_array_get_size(v_buckets_838_);
v___x_843_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_835_);
v___x_844_ = 32ULL;
v___x_845_ = lean_uint64_shift_right(v___x_843_, v___x_844_);
v_fold_846_ = lean_uint64_xor(v___x_843_, v___x_845_);
v___x_847_ = 16ULL;
v___x_848_ = lean_uint64_shift_right(v_fold_846_, v___x_847_);
v___x_849_ = lean_uint64_xor(v_fold_846_, v___x_848_);
v___x_850_ = lean_uint64_to_usize(v___x_849_);
v___x_851_ = lean_usize_of_nat(v___x_842_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_sub(v___x_851_, v___x_852_);
v___x_854_ = lean_usize_land(v___x_850_, v___x_853_);
v_bkt_855_ = lean_array_uget_borrowed(v_buckets_838_, v___x_854_);
v___x_856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_835_, v_bkt_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v_size_x27_858_; lean_object* v___x_859_; lean_object* v_buckets_x27_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v_size_x27_858_ = lean_nat_add(v_size_837_, v___x_857_);
lean_dec(v_size_837_);
lean_inc(v_bkt_855_);
v___x_859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_859_, 0, v_a_835_);
lean_ctor_set(v___x_859_, 1, v_b_836_);
lean_ctor_set(v___x_859_, 2, v_bkt_855_);
v_buckets_x27_860_ = lean_array_uset(v_buckets_838_, v___x_854_, v___x_859_);
v___x_861_ = lean_unsigned_to_nat(4u);
v___x_862_ = lean_nat_mul(v_size_x27_858_, v___x_861_);
v___x_863_ = lean_unsigned_to_nat(3u);
v___x_864_ = lean_nat_div(v___x_862_, v___x_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_array_get_size(v_buckets_x27_860_);
v___x_866_ = lean_nat_dec_le(v___x_864_, v___x_865_);
lean_dec(v___x_864_);
if (v___x_866_ == 0)
{
lean_object* v_val_867_; lean_object* v___x_869_; 
v_val_867_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_860_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_val_867_);
lean_ctor_set(v___x_840_, 0, v_size_x27_858_);
v___x_869_ = v___x_840_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_size_x27_858_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_val_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
lean_object* v___x_872_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_buckets_x27_860_);
lean_ctor_set(v___x_840_, 0, v_size_x27_858_);
v___x_872_ = v___x_840_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_size_x27_858_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_buckets_x27_860_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v___x_874_; lean_object* v_buckets_x27_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc(v_bkt_855_);
v___x_874_ = lean_box(0);
v_buckets_x27_875_ = lean_array_uset(v_buckets_838_, v___x_854_, v___x_874_);
v___x_876_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_835_, v_b_836_, v_bkt_855_);
v___x_877_ = lean_array_uset(v_buckets_x27_875_, v___x_854_, v___x_876_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_877_);
v___x_879_ = v___x_840_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_size_837_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_val_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
uint8_t v___x_884_; 
v___x_884_ = 0;
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v_arg_887_; size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v_head_885_ = lean_ctor_get(v_x_883_, 0);
v_tail_886_ = lean_ctor_get(v_x_883_, 1);
v_arg_887_ = lean_ctor_get(v_head_885_, 0);
v___x_888_ = lean_ptr_addr(v_val_882_);
v___x_889_ = lean_ptr_addr(v_arg_887_);
v___x_890_ = lean_usize_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
v_x_883_ = v_tail_886_;
goto _start;
}
else
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_val_892_, lean_object* v_x_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_892_, v_x_893_);
lean_dec(v_x_893_);
lean_dec_ref(v_val_892_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_908_ = l_Lean_Name_append(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_e_915_, lean_object* v_ctx_916_, lean_object* v___x_917_, lean_object* v_as_918_, size_t v_sz_919_, size_t v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_a_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v___x_917_);
lean_dec_ref(v_ctx_916_);
lean_dec_ref(v_e_915_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_921_);
return v___x_939_;
}
else
{
lean_object* v_snd_940_; lean_object* v_fst_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_1053_; 
v_snd_940_ = lean_ctor_get(v_b_921_, 1);
v_fst_941_ = lean_ctor_get(v_b_921_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_b_921_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_943_ = v_b_921_;
v_isShared_944_ = v_isSharedCheck_1053_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_941_);
lean_dec(v_b_921_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_1053_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1052_; 
v_fst_945_ = lean_ctor_get(v_snd_940_, 0);
v_snd_946_ = lean_ctor_get(v_snd_940_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_snd_940_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_948_ = v_snd_940_;
v_isShared_949_ = v_isSharedCheck_1052_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_946_);
lean_inc(v_fst_945_);
lean_dec(v_snd_940_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1052_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_map_951_; lean_object* v_candidates_952_; lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_a_961_ = lean_array_uget_borrowed(v_as_918_, v_i_920_);
v___x_962_ = lean_st_ref_get(v___y_922_);
v___x_963_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_962_, v_a_961_);
lean_dec(v___x_962_);
if (lean_obj_tag(v___x_963_) == 1)
{
lean_object* v_val_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1049_; 
v_val_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_1049_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_val_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1049_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v_hasTheoryVar_1008_; lean_object* v___x_1009_; 
v_hasTheoryVar_1008_ = lean_ctor_get(v_ctx_916_, 1);
lean_inc_ref(v_hasTheoryVar_1008_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc(v___y_922_);
lean_inc(v_val_964_);
v___x_1009_ = lean_apply_12(v_hasTheoryVar_1008_, v_val_964_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, lean_box(0));
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; uint8_t v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_unbox(v_a_1010_);
lean_dec(v_a_1010_);
if (v___x_1011_ == 0)
{
lean_del_object(v___x_966_);
lean_dec(v_val_964_);
v_map_951_ = v_fst_941_;
v_candidates_952_ = v_fst_945_;
goto v___jp_950_;
}
else
{
lean_object* v_toCold_1012_; lean_object* v_options_1013_; uint8_t v_hasTrace_1014_; 
v_toCold_1012_ = lean_ctor_get(v___y_930_, 0);
v_options_1013_ = lean_ctor_get(v_toCold_1012_, 2);
v_hasTrace_1014_ = lean_ctor_get_uint8(v_options_1013_, sizeof(void*)*1);
if (v_hasTrace_1014_ == 0)
{
lean_del_object(v___x_966_);
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
v___y_977_ = v___y_930_;
v___y_978_ = v___y_931_;
goto v___jp_968_;
}
else
{
lean_object* v_inheritedTraceOptions_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_inheritedTraceOptions_1015_ = lean_ctor_get(v_toCold_1012_, 11);
v___x_1016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3));
v___x_1017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
v___x_1018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1015_, v_options_1013_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_del_object(v___x_966_);
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
v___y_977_ = v___y_930_;
v___y_978_ = v___y_931_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc(v_val_964_);
v___x_1019_ = l_Lean_MessageData_ofExpr(v_val_964_);
v___x_1020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
lean_inc_ref(v___x_917_);
v___x_1022_ = l_Lean_MessageData_ofExpr(v___x_917_);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
lean_inc(v_snd_946_);
v___x_1026_ = l_Nat_reprFast(v_snd_946_);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 3);
lean_ctor_set(v___x_966_, 0, v___x_1026_);
v___x_1028_ = v___x_966_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = l_Lean_MessageData_ofFormat(v___x_1028_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1025_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1016_, v___x_1030_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec_ref_known(v___x_1031_, 1);
v___y_969_ = v___y_922_;
v___y_970_ = v___y_923_;
v___y_971_ = v___y_924_;
v___y_972_ = v___y_925_;
v___y_973_ = v___y_926_;
v___y_974_ = v___y_927_;
v___y_975_ = v___y_928_;
v___y_976_ = v___y_929_;
v___y_977_ = v___y_930_;
v___y_978_ = v___y_931_;
goto v___jp_968_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_val_964_);
lean_del_object(v___x_948_);
lean_dec(v_snd_946_);
lean_dec(v_fst_945_);
lean_del_object(v___x_943_);
lean_dec(v_fst_941_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v_ctx_916_);
lean_dec_ref(v_e_915_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
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
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_del_object(v___x_966_);
lean_dec(v_val_964_);
lean_del_object(v___x_948_);
lean_dec(v_snd_946_);
lean_dec(v_fst_945_);
lean_del_object(v___x_943_);
lean_dec(v_fst_941_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v_ctx_916_);
lean_dec_ref(v_e_915_);
v_a_1041_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1009_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1009_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
v___jp_968_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_inc_ref_n(v_e_915_, 2);
lean_inc(v_val_964_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_val_964_);
lean_ctor_set(v___x_979_, 1, v_e_915_);
v___x_980_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_915_, v_snd_946_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_941_, v_a_981_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; uint8_t v___x_984_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_964_, v_val_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_inc(v_snd_946_);
lean_inc_ref(v___x_979_);
lean_inc_ref(v_ctx_916_);
v___x_985_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_916_, v_val_964_, v___x_979_, v_snd_946_, v_val_983_, v_fst_945_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_979_);
lean_ctor_set(v___x_987_, 1, v_val_983_);
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_941_, v_a_981_, v___x_987_);
v_map_951_ = v___x_988_;
v_candidates_952_ = v_a_986_;
goto v___jp_950_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_val_983_);
lean_dec(v_a_981_);
lean_dec_ref_known(v___x_979_, 2);
lean_del_object(v___x_948_);
lean_dec(v_snd_946_);
lean_del_object(v___x_943_);
lean_dec(v_fst_941_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v_ctx_916_);
lean_dec_ref(v_e_915_);
v_a_989_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_985_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_dec(v_val_983_);
lean_dec(v_a_981_);
lean_dec_ref_known(v___x_979_, 2);
lean_dec(v_val_964_);
v_map_951_ = v_fst_941_;
v_candidates_952_ = v_fst_945_;
goto v___jp_950_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v___x_982_);
lean_dec(v_val_964_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_979_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_941_, v_a_981_, v___x_998_);
v_map_951_ = v___x_999_;
v_candidates_952_ = v_fst_945_;
goto v___jp_950_;
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref_known(v___x_979_, 2);
lean_dec(v_val_964_);
lean_del_object(v___x_948_);
lean_dec(v_snd_946_);
lean_dec(v_fst_945_);
lean_del_object(v___x_943_);
lean_dec(v_fst_941_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v_ctx_916_);
lean_dec_ref(v_e_915_);
v_a_1000_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_980_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_980_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec(v___x_963_);
lean_del_object(v___x_948_);
lean_del_object(v___x_943_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_fst_945_);
lean_ctor_set(v___x_1050_, 1, v_snd_946_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_fst_941_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v_a_934_ = v___x_1051_;
goto v___jp_933_;
}
v___jp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_snd_946_, v___x_953_);
lean_dec(v_snd_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_954_);
lean_ctor_set(v___x_948_, 0, v_candidates_952_);
v___x_956_ = v___x_948_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_candidates_952_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_954_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_956_);
lean_ctor_set(v___x_943_, 0, v_map_951_);
v___x_958_ = v___x_943_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_map_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_a_934_ = v___x_958_;
goto v___jp_933_;
}
}
}
}
}
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_920_, v___x_935_);
v_i_920_ = v___x_936_;
v_b_921_ = v_a_934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object** _args){
lean_object* v_e_1054_ = _args[0];
lean_object* v_ctx_1055_ = _args[1];
lean_object* v___x_1056_ = _args[2];
lean_object* v_as_1057_ = _args[3];
lean_object* v_sz_1058_ = _args[4];
lean_object* v_i_1059_ = _args[5];
lean_object* v_b_1060_ = _args[6];
lean_object* v___y_1061_ = _args[7];
lean_object* v___y_1062_ = _args[8];
lean_object* v___y_1063_ = _args[9];
lean_object* v___y_1064_ = _args[10];
lean_object* v___y_1065_ = _args[11];
lean_object* v___y_1066_ = _args[12];
lean_object* v___y_1067_ = _args[13];
lean_object* v___y_1068_ = _args[14];
lean_object* v___y_1069_ = _args[15];
lean_object* v___y_1070_ = _args[16];
lean_object* v___y_1071_ = _args[17];
_start:
{
size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1058_);
lean_dec(v_sz_1058_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_1054_, v_ctx_1055_, v___x_1056_, v_as_1057_, v_sz_boxed_1072_, v_i_boxed_1073_, v_b_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v_as_1057_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(lean_object* v_ctx_1075_, uint8_t v_a_1076_, lean_object* v_as_1077_, size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref(v_ctx_1075_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_b_1080_);
return v___x_1093_;
}
else
{
lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1196_; 
v_snd_1094_ = lean_ctor_get(v_b_1080_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_b_1080_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_b_1080_, 0);
lean_dec(v_unused_1197_);
v___x_1096_ = v_b_1080_;
v_isShared_1097_ = v_isSharedCheck_1196_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_dec(v_b_1080_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1196_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1195_; 
v_fst_1098_ = lean_ctor_get(v_snd_1094_, 0);
v_snd_1099_ = lean_ctor_get(v_snd_1094_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_snd_1094_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1101_ = v_snd_1094_;
v_isShared_1102_ = v_isSharedCheck_1195_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_snd_1094_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1195_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v_a_1105_; lean_object* v_a_1118_; uint8_t v___y_1192_; uint8_t v___x_1193_; 
v___x_1103_ = lean_box(0);
v_a_1118_ = lean_array_uget_borrowed(v_as_1077_, v_i_1079_);
v___x_1193_ = l_Lean_Expr_isApp(v_a_1118_);
if (v___x_1193_ == 0)
{
v___y_1192_ = v_a_1076_;
goto v___jp_1191_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_Expr_isEq(v_a_1118_);
if (v___x_1194_ == 0)
{
goto v___jp_1119_;
}
else
{
v___y_1192_ = v_a_1076_;
goto v___jp_1191_;
}
}
v___jp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_a_1105_);
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1107_ = v___x_1101_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1105_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
size_t v___x_1108_; size_t v___x_1109_; 
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1079_, v___x_1108_);
v_i_1079_ = v___x_1109_;
v_b_1080_ = v___x_1107_;
goto _start;
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_snd_1099_);
lean_ctor_set(v___x_1096_, 0, v_fst_1098_);
v___x_1114_ = v___x_1096_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_fst_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_snd_1099_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
v_a_1105_ = v___x_1114_;
goto v___jp_1104_;
}
}
v___jp_1116_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_fst_1098_);
lean_ctor_set(v___x_1117_, 1, v_snd_1099_);
v_a_1105_ = v___x_1117_;
goto v___jp_1104_;
}
v___jp_1119_:
{
uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_Expr_isHEq(v_a_1118_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_inc(v_a_1118_);
v___x_1121_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1118_, v___y_1081_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
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
lean_object* v___x_1124_; 
lean_del_object(v___x_1096_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_fst_1098_);
lean_ctor_set(v___x_1124_, 1, v_snd_1099_);
v_a_1105_ = v___x_1124_;
goto v___jp_1104_;
}
else
{
lean_object* v_isInterpreted_1125_; lean_object* v___x_1126_; 
v_isInterpreted_1125_ = lean_ctor_get(v_ctx_1075_, 0);
lean_inc_ref(v_isInterpreted_1125_);
lean_inc(v___y_1090_);
lean_inc_ref(v___y_1089_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc(v_a_1118_);
v___x_1126_ = lean_apply_12(v_isInterpreted_1125_, v_a_1118_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, lean_box(0));
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; uint8_t v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l_Lean_Expr_getAppFn(v_a_1118_);
lean_inc_ref(v___x_1129_);
v___x_1130_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1129_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; uint8_t v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1129_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v_dummy_1135_; lean_object* v_nargs_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
lean_del_object(v___x_1096_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v_dummy_1135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1136_ = l_Lean_Expr_getAppNumArgs(v_a_1118_);
lean_inc(v_nargs_1136_);
v___x_1137_ = lean_mk_array(v_nargs_1136_, v_dummy_1135_);
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_sub(v_nargs_1136_, v___x_1138_);
lean_dec(v_nargs_1136_);
lean_inc_n(v_a_1118_, 2);
v___x_1140_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1118_, v___x_1137_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_snd_1099_);
lean_ctor_set(v___x_1141_, 1, v___x_1134_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_fst_1098_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v_sz_1143_ = lean_array_size(v___x_1140_);
v___x_1144_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1075_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1118_, v_ctx_1075_, v___x_1129_, v___x_1140_, v_sz_1143_, v___x_1144_, v___x_1142_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec_ref(v___x_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_snd_1147_; lean_object* v_fst_1148_; lean_object* v_fst_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v_snd_1147_ = lean_ctor_get(v_a_1146_, 1);
lean_inc(v_snd_1147_);
v_fst_1148_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_fst_1148_);
lean_dec(v_a_1146_);
v_fst_1149_ = lean_ctor_get(v_snd_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_snd_1147_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_snd_1147_, 1);
lean_dec(v_unused_1157_);
v___x_1151_ = v_snd_1147_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_fst_1149_);
lean_dec(v_snd_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_fst_1149_);
lean_ctor_set(v___x_1151_, 0, v_fst_1148_);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_fst_1148_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_fst_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
v_a_1105_ = v___x_1154_;
goto v___jp_1104_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_del_object(v___x_1101_);
lean_dec_ref(v_ctx_1075_);
v_a_1158_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1145_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1145_);
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
lean_dec_ref(v___x_1129_);
goto v___jp_1112_;
}
}
else
{
lean_dec_ref(v___x_1129_);
goto v___jp_1112_;
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v___x_1129_);
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_ctx_1075_);
v_a_1166_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1130_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1130_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v___x_1174_; 
lean_del_object(v___x_1096_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_fst_1098_);
lean_ctor_set(v___x_1174_, 1, v_snd_1099_);
v_a_1105_ = v___x_1174_;
goto v___jp_1104_;
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_ctx_1075_);
v_a_1175_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1126_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1126_);
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
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1101_);
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_del_object(v___x_1096_);
lean_dec_ref(v_ctx_1075_);
v_a_1183_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1121_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1121_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_del_object(v___x_1096_);
goto v___jp_1116_;
}
}
v___jp_1191_:
{
if (v___y_1192_ == 0)
{
lean_del_object(v___x_1096_);
goto v___jp_1116_;
}
else
{
goto v___jp_1119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(lean_object** _args){
lean_object* v_ctx_1198_ = _args[0];
lean_object* v_a_1199_ = _args[1];
lean_object* v_as_1200_ = _args[2];
lean_object* v_sz_1201_ = _args[3];
lean_object* v_i_1202_ = _args[4];
lean_object* v_b_1203_ = _args[5];
lean_object* v___y_1204_ = _args[6];
lean_object* v___y_1205_ = _args[7];
lean_object* v___y_1206_ = _args[8];
lean_object* v___y_1207_ = _args[9];
lean_object* v___y_1208_ = _args[10];
lean_object* v___y_1209_ = _args[11];
lean_object* v___y_1210_ = _args[12];
lean_object* v___y_1211_ = _args[13];
lean_object* v___y_1212_ = _args[14];
lean_object* v___y_1213_ = _args[15];
lean_object* v___y_1214_ = _args[16];
_start:
{
uint8_t v_a_162417__boxed_1215_; size_t v_sz_boxed_1216_; size_t v_i_boxed_1217_; lean_object* v_res_1218_; 
v_a_162417__boxed_1215_ = lean_unbox(v_a_1199_);
v_sz_boxed_1216_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1217_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1198_, v_a_162417__boxed_1215_, v_as_1200_, v_sz_boxed_1216_, v_i_boxed_1217_, v_b_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v_as_1200_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(lean_object* v_ctx_1219_, uint8_t v_a_1220_, lean_object* v_as_1221_, size_t v_sz_1222_, size_t v_i_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v___x_1236_; 
v___x_1236_ = lean_usize_dec_lt(v_i_1223_, v_sz_1222_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v_ctx_1219_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_b_1224_);
return v___x_1237_;
}
else
{
lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1340_; 
v_snd_1238_ = lean_ctor_get(v_b_1224_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_b_1224_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_b_1224_, 0);
lean_dec(v_unused_1341_);
v___x_1240_ = v_b_1224_;
v_isShared_1241_ = v_isSharedCheck_1340_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_dec(v_b_1224_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1340_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1339_; 
v_fst_1242_ = lean_ctor_get(v_snd_1238_, 0);
v_snd_1243_ = lean_ctor_get(v_snd_1238_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_snd_1238_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1245_ = v_snd_1238_;
v_isShared_1246_ = v_isSharedCheck_1339_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1242_);
lean_dec(v_snd_1238_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1339_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v_a_1249_; lean_object* v_a_1262_; uint8_t v___y_1336_; uint8_t v___x_1337_; 
v___x_1247_ = lean_box(0);
v_a_1262_ = lean_array_uget_borrowed(v_as_1221_, v_i_1223_);
v___x_1337_ = l_Lean_Expr_isApp(v_a_1262_);
if (v___x_1337_ == 0)
{
v___y_1336_ = v_a_1220_;
goto v___jp_1335_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Lean_Expr_isEq(v_a_1262_);
if (v___x_1338_ == 0)
{
goto v___jp_1263_;
}
else
{
v___y_1336_ = v_a_1220_;
goto v___jp_1335_;
}
}
v___jp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_a_1249_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_a_1249_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_add(v_i_1223_, v___x_1252_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_1219_, v_a_1220_, v_as_1221_, v_sz_1222_, v___x_1253_, v___x_1251_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1254_;
}
}
v___jp_1256_:
{
lean_object* v___x_1258_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v_snd_1243_);
lean_ctor_set(v___x_1240_, 0, v_fst_1242_);
v___x_1258_ = v___x_1240_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_fst_1242_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_snd_1243_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_a_1249_ = v___x_1258_;
goto v___jp_1248_;
}
}
v___jp_1260_:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_fst_1242_);
lean_ctor_set(v___x_1261_, 1, v_snd_1243_);
v_a_1249_ = v___x_1261_;
goto v___jp_1248_;
}
v___jp_1263_:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Lean_Expr_isHEq(v_a_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_inc(v_a_1262_);
v___x_1265_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1262_, v___y_1225_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
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
lean_object* v___x_1268_; 
lean_del_object(v___x_1240_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_fst_1242_);
lean_ctor_set(v___x_1268_, 1, v_snd_1243_);
v_a_1249_ = v___x_1268_;
goto v___jp_1248_;
}
else
{
lean_object* v_isInterpreted_1269_; lean_object* v___x_1270_; 
v_isInterpreted_1269_ = lean_ctor_get(v_ctx_1219_, 0);
lean_inc_ref(v_isInterpreted_1269_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1227_);
lean_inc(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc(v_a_1262_);
v___x_1270_ = lean_apply_12(v_isInterpreted_1269_, v_a_1262_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, lean_box(0));
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; uint8_t v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = l_Lean_Expr_getAppFn(v_a_1262_);
lean_inc_ref(v___x_1273_);
v___x_1274_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1273_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1273_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v_dummy_1279_; lean_object* v_nargs_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; size_t v_sz_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
lean_del_object(v___x_1240_);
v___x_1278_ = lean_unsigned_to_nat(0u);
v_dummy_1279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1280_ = l_Lean_Expr_getAppNumArgs(v_a_1262_);
lean_inc(v_nargs_1280_);
v___x_1281_ = lean_mk_array(v_nargs_1280_, v_dummy_1279_);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_sub(v_nargs_1280_, v___x_1282_);
lean_dec(v_nargs_1280_);
lean_inc_n(v_a_1262_, 2);
v___x_1284_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1262_, v___x_1281_, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_snd_1243_);
lean_ctor_set(v___x_1285_, 1, v___x_1278_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_fst_1242_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v_sz_1287_ = lean_array_size(v___x_1284_);
v___x_1288_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1219_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1262_, v_ctx_1219_, v___x_1273_, v___x_1284_, v_sz_1287_, v___x_1288_, v___x_1286_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec_ref(v___x_1284_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_snd_1291_; lean_object* v_fst_1292_; lean_object* v_fst_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v_snd_1291_ = lean_ctor_get(v_a_1290_, 1);
lean_inc(v_snd_1291_);
v_fst_1292_ = lean_ctor_get(v_a_1290_, 0);
lean_inc(v_fst_1292_);
lean_dec(v_a_1290_);
v_fst_1293_ = lean_ctor_get(v_snd_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_snd_1291_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_snd_1291_, 1);
lean_dec(v_unused_1301_);
v___x_1295_ = v_snd_1291_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_fst_1293_);
lean_dec(v_snd_1291_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v_fst_1293_);
lean_ctor_set(v___x_1295_, 0, v_fst_1292_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_fst_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_fst_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v_a_1249_ = v___x_1298_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v_ctx_1219_);
v_a_1302_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1289_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1289_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_dec_ref(v___x_1273_);
goto v___jp_1256_;
}
}
else
{
lean_dec_ref(v___x_1273_);
goto v___jp_1256_;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___x_1273_);
lean_del_object(v___x_1245_);
lean_dec(v_snd_1243_);
lean_dec(v_fst_1242_);
lean_del_object(v___x_1240_);
lean_dec_ref(v_ctx_1219_);
v_a_1310_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1274_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1274_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v___x_1318_; 
lean_del_object(v___x_1240_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_fst_1242_);
lean_ctor_set(v___x_1318_, 1, v_snd_1243_);
v_a_1249_ = v___x_1318_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_del_object(v___x_1245_);
lean_dec(v_snd_1243_);
lean_dec(v_fst_1242_);
lean_del_object(v___x_1240_);
lean_dec_ref(v_ctx_1219_);
v_a_1319_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1270_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1270_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1245_);
lean_dec(v_snd_1243_);
lean_dec(v_fst_1242_);
lean_del_object(v___x_1240_);
lean_dec_ref(v_ctx_1219_);
v_a_1327_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1265_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1265_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_del_object(v___x_1240_);
goto v___jp_1260_;
}
}
v___jp_1335_:
{
if (v___y_1336_ == 0)
{
lean_del_object(v___x_1240_);
goto v___jp_1260_;
}
else
{
goto v___jp_1263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(lean_object** _args){
lean_object* v_ctx_1342_ = _args[0];
lean_object* v_a_1343_ = _args[1];
lean_object* v_as_1344_ = _args[2];
lean_object* v_sz_1345_ = _args[3];
lean_object* v_i_1346_ = _args[4];
lean_object* v_b_1347_ = _args[5];
lean_object* v___y_1348_ = _args[6];
lean_object* v___y_1349_ = _args[7];
lean_object* v___y_1350_ = _args[8];
lean_object* v___y_1351_ = _args[9];
lean_object* v___y_1352_ = _args[10];
lean_object* v___y_1353_ = _args[11];
lean_object* v___y_1354_ = _args[12];
lean_object* v___y_1355_ = _args[13];
lean_object* v___y_1356_ = _args[14];
lean_object* v___y_1357_ = _args[15];
lean_object* v___y_1358_ = _args[16];
_start:
{
uint8_t v_a_162645__boxed_1359_; size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_a_162645__boxed_1359_ = lean_unbox(v_a_1343_);
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1342_, v_a_162645__boxed_1359_, v_as_1344_, v_sz_boxed_1360_, v_i_boxed_1361_, v_b_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v_as_1344_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(lean_object* v_ctx_1363_, uint8_t v_a_1364_, lean_object* v_as_1365_, size_t v_sz_1366_, size_t v_i_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_lt(v_i_1367_, v_sz_1366_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref(v_ctx_1363_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_b_1368_);
return v___x_1381_;
}
else
{
lean_object* v_snd_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1484_; 
v_snd_1382_ = lean_ctor_get(v_b_1368_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_b_1368_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_b_1368_, 0);
lean_dec(v_unused_1485_);
v___x_1384_ = v_b_1368_;
v_isShared_1385_ = v_isSharedCheck_1484_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_snd_1382_);
lean_dec(v_b_1368_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1484_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_fst_1386_; lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1483_; 
v_fst_1386_ = lean_ctor_get(v_snd_1382_, 0);
v_snd_1387_ = lean_ctor_get(v_snd_1382_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_snd_1382_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1389_ = v_snd_1382_;
v_isShared_1390_ = v_isSharedCheck_1483_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_inc(v_fst_1386_);
lean_dec(v_snd_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1483_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v_a_1393_; lean_object* v_a_1406_; uint8_t v___y_1480_; uint8_t v___x_1481_; 
v___x_1391_ = lean_box(0);
v_a_1406_ = lean_array_uget_borrowed(v_as_1365_, v_i_1367_);
v___x_1481_ = l_Lean_Expr_isApp(v_a_1406_);
if (v___x_1481_ == 0)
{
v___y_1480_ = v_a_1364_;
goto v___jp_1479_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Lean_Expr_isEq(v_a_1406_);
if (v___x_1482_ == 0)
{
goto v___jp_1407_;
}
else
{
v___y_1480_ = v_a_1364_;
goto v___jp_1479_;
}
}
v___jp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_a_1393_);
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_a_1393_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
size_t v___x_1396_; size_t v___x_1397_; 
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1367_, v___x_1396_);
v_i_1367_ = v___x_1397_;
v_b_1368_ = v___x_1395_;
goto _start;
}
}
v___jp_1400_:
{
lean_object* v___x_1402_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_snd_1387_);
lean_ctor_set(v___x_1384_, 0, v_fst_1386_);
v___x_1402_ = v___x_1384_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_fst_1386_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1387_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v_a_1393_ = v___x_1402_;
goto v___jp_1392_;
}
}
v___jp_1404_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_fst_1386_);
lean_ctor_set(v___x_1405_, 1, v_snd_1387_);
v_a_1393_ = v___x_1405_;
goto v___jp_1392_;
}
v___jp_1407_:
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Expr_isHEq(v_a_1406_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_inc(v_a_1406_);
v___x_1409_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1406_, v___y_1369_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
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
lean_object* v___x_1412_; 
lean_del_object(v___x_1384_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_fst_1386_);
lean_ctor_set(v___x_1412_, 1, v_snd_1387_);
v_a_1393_ = v___x_1412_;
goto v___jp_1392_;
}
else
{
lean_object* v_isInterpreted_1413_; lean_object* v___x_1414_; 
v_isInterpreted_1413_ = lean_ctor_get(v_ctx_1363_, 0);
lean_inc_ref(v_isInterpreted_1413_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc(v_a_1406_);
v___x_1414_ = lean_apply_12(v_isInterpreted_1413_, v_a_1406_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, lean_box(0));
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; uint8_t v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = lean_unbox(v_a_1415_);
lean_dec(v_a_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = l_Lean_Expr_getAppFn(v_a_1406_);
lean_inc_ref(v___x_1417_);
v___x_1418_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1417_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; uint8_t v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_unbox(v_a_1419_);
lean_dec(v_a_1419_);
if (v___x_1420_ == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1417_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v_dummy_1423_; lean_object* v_nargs_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; size_t v_sz_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
lean_del_object(v___x_1384_);
v___x_1422_ = lean_unsigned_to_nat(0u);
v_dummy_1423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1424_ = l_Lean_Expr_getAppNumArgs(v_a_1406_);
lean_inc(v_nargs_1424_);
v___x_1425_ = lean_mk_array(v_nargs_1424_, v_dummy_1423_);
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = lean_nat_sub(v_nargs_1424_, v___x_1426_);
lean_dec(v_nargs_1424_);
lean_inc_n(v_a_1406_, 2);
v___x_1428_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1406_, v___x_1425_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_snd_1387_);
lean_ctor_set(v___x_1429_, 1, v___x_1422_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_fst_1386_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v_sz_1431_ = lean_array_size(v___x_1428_);
v___x_1432_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1363_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1406_, v_ctx_1363_, v___x_1417_, v___x_1428_, v_sz_1431_, v___x_1432_, v___x_1430_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___x_1428_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v_snd_1435_; lean_object* v_fst_1436_; lean_object* v_fst_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v_snd_1435_ = lean_ctor_get(v_a_1434_, 1);
lean_inc(v_snd_1435_);
v_fst_1436_ = lean_ctor_get(v_a_1434_, 0);
lean_inc(v_fst_1436_);
lean_dec(v_a_1434_);
v_fst_1437_ = lean_ctor_get(v_snd_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_snd_1435_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_snd_1435_, 1);
lean_dec(v_unused_1445_);
v___x_1439_ = v_snd_1435_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_fst_1437_);
lean_dec(v_snd_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_fst_1437_);
lean_ctor_set(v___x_1439_, 0, v_fst_1436_);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_fst_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_fst_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v_a_1393_ = v___x_1442_;
goto v___jp_1392_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1389_);
lean_dec_ref(v_ctx_1363_);
v_a_1446_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1433_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1433_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_dec_ref(v___x_1417_);
goto v___jp_1400_;
}
}
else
{
lean_dec_ref(v___x_1417_);
goto v___jp_1400_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v___x_1417_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_del_object(v___x_1384_);
lean_dec_ref(v_ctx_1363_);
v_a_1454_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1418_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1418_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1462_; 
lean_del_object(v___x_1384_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_fst_1386_);
lean_ctor_set(v___x_1462_, 1, v_snd_1387_);
v_a_1393_ = v___x_1462_;
goto v___jp_1392_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_del_object(v___x_1384_);
lean_dec_ref(v_ctx_1363_);
v_a_1463_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1414_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1414_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_del_object(v___x_1384_);
lean_dec_ref(v_ctx_1363_);
v_a_1471_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1409_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1409_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_del_object(v___x_1384_);
goto v___jp_1404_;
}
}
v___jp_1479_:
{
if (v___y_1480_ == 0)
{
lean_del_object(v___x_1384_);
goto v___jp_1404_;
}
else
{
goto v___jp_1407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(lean_object** _args){
lean_object* v_ctx_1486_ = _args[0];
lean_object* v_a_1487_ = _args[1];
lean_object* v_as_1488_ = _args[2];
lean_object* v_sz_1489_ = _args[3];
lean_object* v_i_1490_ = _args[4];
lean_object* v_b_1491_ = _args[5];
lean_object* v___y_1492_ = _args[6];
lean_object* v___y_1493_ = _args[7];
lean_object* v___y_1494_ = _args[8];
lean_object* v___y_1495_ = _args[9];
lean_object* v___y_1496_ = _args[10];
lean_object* v___y_1497_ = _args[11];
lean_object* v___y_1498_ = _args[12];
lean_object* v___y_1499_ = _args[13];
lean_object* v___y_1500_ = _args[14];
lean_object* v___y_1501_ = _args[15];
lean_object* v___y_1502_ = _args[16];
_start:
{
uint8_t v_a_162873__boxed_1503_; size_t v_sz_boxed_1504_; size_t v_i_boxed_1505_; lean_object* v_res_1506_; 
v_a_162873__boxed_1503_ = lean_unbox(v_a_1487_);
v_sz_boxed_1504_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1505_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1486_, v_a_162873__boxed_1503_, v_as_1488_, v_sz_boxed_1504_, v_i_boxed_1505_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v_as_1488_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(lean_object* v_ctx_1507_, uint8_t v_a_1508_, lean_object* v_as_1509_, size_t v_sz_1510_, size_t v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1511_, v_sz_1510_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_dec_ref(v_ctx_1507_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1512_);
return v___x_1525_;
}
else
{
lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1628_; 
v_snd_1526_ = lean_ctor_get(v_b_1512_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_b_1512_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_b_1512_, 0);
lean_dec(v_unused_1629_);
v___x_1528_ = v_b_1512_;
v_isShared_1529_ = v_isSharedCheck_1628_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v_b_1512_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1628_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_fst_1530_; lean_object* v_snd_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1627_; 
v_fst_1530_ = lean_ctor_get(v_snd_1526_, 0);
v_snd_1531_ = lean_ctor_get(v_snd_1526_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_snd_1526_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1533_ = v_snd_1526_;
v_isShared_1534_ = v_isSharedCheck_1627_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_snd_1531_);
lean_inc(v_fst_1530_);
lean_dec(v_snd_1526_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1627_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v_a_1537_; lean_object* v_a_1550_; uint8_t v___y_1624_; uint8_t v___x_1625_; 
v___x_1535_ = lean_box(0);
v_a_1550_ = lean_array_uget_borrowed(v_as_1509_, v_i_1511_);
v___x_1625_ = l_Lean_Expr_isApp(v_a_1550_);
if (v___x_1625_ == 0)
{
v___y_1624_ = v_a_1508_;
goto v___jp_1623_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Lean_Expr_isEq(v_a_1550_);
if (v___x_1626_ == 0)
{
goto v___jp_1551_;
}
else
{
v___y_1624_ = v_a_1508_;
goto v___jp_1623_;
}
}
v___jp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_a_1537_);
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1539_ = v___x_1533_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_a_1537_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1511_, v___x_1540_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_1507_, v_a_1508_, v_as_1509_, v_sz_1510_, v___x_1541_, v___x_1539_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1542_;
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_snd_1531_);
lean_ctor_set(v___x_1528_, 0, v_fst_1530_);
v___x_1546_ = v___x_1528_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_fst_1530_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_snd_1531_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v_a_1537_ = v___x_1546_;
goto v___jp_1536_;
}
}
v___jp_1548_:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_fst_1530_);
lean_ctor_set(v___x_1549_, 1, v_snd_1531_);
v_a_1537_ = v___x_1549_;
goto v___jp_1536_;
}
v___jp_1551_:
{
uint8_t v___x_1552_; 
v___x_1552_ = l_Lean_Expr_isHEq(v_a_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_inc(v_a_1550_);
v___x_1553_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1550_, v___y_1513_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
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
lean_object* v___x_1556_; 
lean_del_object(v___x_1528_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_fst_1530_);
lean_ctor_set(v___x_1556_, 1, v_snd_1531_);
v_a_1537_ = v___x_1556_;
goto v___jp_1536_;
}
else
{
lean_object* v_isInterpreted_1557_; lean_object* v___x_1558_; 
v_isInterpreted_1557_ = lean_ctor_get(v_ctx_1507_, 0);
lean_inc_ref(v_isInterpreted_1557_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc(v_a_1550_);
v___x_1558_ = lean_apply_12(v_isInterpreted_1557_, v_a_1550_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; uint8_t v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Lean_Expr_getAppFn(v_a_1550_);
lean_inc_ref(v___x_1561_);
v___x_1562_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1561_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; uint8_t v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = lean_unbox(v_a_1563_);
lean_dec(v_a_1563_);
if (v___x_1564_ == 0)
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1561_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v_dummy_1567_; lean_object* v_nargs_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1528_);
v___x_1566_ = lean_unsigned_to_nat(0u);
v_dummy_1567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1568_ = l_Lean_Expr_getAppNumArgs(v_a_1550_);
lean_inc(v_nargs_1568_);
v___x_1569_ = lean_mk_array(v_nargs_1568_, v_dummy_1567_);
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_sub(v_nargs_1568_, v___x_1570_);
lean_dec(v_nargs_1568_);
lean_inc_n(v_a_1550_, 2);
v___x_1572_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1550_, v___x_1569_, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_snd_1531_);
lean_ctor_set(v___x_1573_, 1, v___x_1566_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_fst_1530_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v_sz_1575_ = lean_array_size(v___x_1572_);
v___x_1576_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1507_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_1550_, v_ctx_1507_, v___x_1561_, v___x_1572_, v_sz_1575_, v___x_1576_, v___x_1574_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___x_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_snd_1579_; lean_object* v_fst_1580_; lean_object* v_fst_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v_snd_1579_ = lean_ctor_get(v_a_1578_, 1);
lean_inc(v_snd_1579_);
v_fst_1580_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_fst_1580_);
lean_dec(v_a_1578_);
v_fst_1581_ = lean_ctor_get(v_snd_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_snd_1579_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v_snd_1579_, 1);
lean_dec(v_unused_1589_);
v___x_1583_ = v_snd_1579_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_fst_1581_);
lean_dec(v_snd_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v_fst_1581_);
lean_ctor_set(v___x_1583_, 0, v_fst_1580_);
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_fst_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_fst_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
v_a_1537_ = v___x_1586_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1533_);
lean_dec_ref(v_ctx_1507_);
v_a_1590_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1577_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1577_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_dec_ref(v___x_1561_);
goto v___jp_1544_;
}
}
else
{
lean_dec_ref(v___x_1561_);
goto v___jp_1544_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v___x_1561_);
lean_del_object(v___x_1533_);
lean_dec(v_snd_1531_);
lean_dec(v_fst_1530_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_ctx_1507_);
v_a_1598_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1562_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1562_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v___x_1606_; 
lean_del_object(v___x_1528_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_fst_1530_);
lean_ctor_set(v___x_1606_, 1, v_snd_1531_);
v_a_1537_ = v___x_1606_;
goto v___jp_1536_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1533_);
lean_dec(v_snd_1531_);
lean_dec(v_fst_1530_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_ctx_1507_);
v_a_1607_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1558_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1558_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1533_);
lean_dec(v_snd_1531_);
lean_dec(v_fst_1530_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_ctx_1507_);
v_a_1615_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1553_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1553_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_del_object(v___x_1528_);
goto v___jp_1548_;
}
}
v___jp_1623_:
{
if (v___y_1624_ == 0)
{
lean_del_object(v___x_1528_);
goto v___jp_1548_;
}
else
{
goto v___jp_1551_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(lean_object** _args){
lean_object* v_ctx_1630_ = _args[0];
lean_object* v_a_1631_ = _args[1];
lean_object* v_as_1632_ = _args[2];
lean_object* v_sz_1633_ = _args[3];
lean_object* v_i_1634_ = _args[4];
lean_object* v_b_1635_ = _args[5];
lean_object* v___y_1636_ = _args[6];
lean_object* v___y_1637_ = _args[7];
lean_object* v___y_1638_ = _args[8];
lean_object* v___y_1639_ = _args[9];
lean_object* v___y_1640_ = _args[10];
lean_object* v___y_1641_ = _args[11];
lean_object* v___y_1642_ = _args[12];
lean_object* v___y_1643_ = _args[13];
lean_object* v___y_1644_ = _args[14];
lean_object* v___y_1645_ = _args[15];
lean_object* v___y_1646_ = _args[16];
_start:
{
uint8_t v_a_163101__boxed_1647_; size_t v_sz_boxed_1648_; size_t v_i_boxed_1649_; lean_object* v_res_1650_; 
v_a_163101__boxed_1647_ = lean_unbox(v_a_1631_);
v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1649_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1630_, v_a_163101__boxed_1647_, v_as_1632_, v_sz_boxed_1648_, v_i_boxed_1649_, v_b_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v_as_1632_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(lean_object* v_init_1651_, lean_object* v_ctx_1652_, uint8_t v_a_1653_, lean_object* v_n_1654_, lean_object* v_b_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
if (lean_obj_tag(v_n_1654_) == 0)
{
lean_object* v_cs_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; size_t v_sz_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v_cs_1667_ = lean_ctor_get(v_n_1654_, 0);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_b_1655_);
v_sz_1670_ = lean_array_size(v_cs_1667_);
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1651_, v_ctx_1652_, v_a_1653_, v_cs_1667_, v_sz_1670_, v___x_1671_, v___x_1669_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1687_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_fst_1677_; 
v_fst_1677_ = lean_ctor_get(v_a_1673_, 0);
if (lean_obj_tag(v_fst_1677_) == 0)
{
lean_object* v_snd_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v_snd_1678_ = lean_ctor_get(v_a_1673_, 1);
lean_inc(v_snd_1678_);
lean_dec(v_a_1673_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_snd_1678_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1679_);
v___x_1681_ = v___x_1675_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1685_; 
lean_inc_ref(v_fst_1677_);
lean_dec(v_a_1673_);
v_val_1683_ = lean_ctor_get(v_fst_1677_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v_fst_1677_, 1);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v_val_1683_);
v___x_1685_ = v___x_1675_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_val_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1672_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1672_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_vs_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; size_t v_sz_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v_vs_1696_ = lean_ctor_get(v_n_1654_, 0);
v___x_1697_ = lean_box(0);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v_b_1655_);
v_sz_1699_ = lean_array_size(v_vs_1696_);
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_1652_, v_a_1653_, v_vs_1696_, v_sz_1699_, v___x_1700_, v___x_1698_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1716_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1716_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1716_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_fst_1706_; 
v_fst_1706_ = lean_ctor_get(v_a_1702_, 0);
if (lean_obj_tag(v_fst_1706_) == 0)
{
lean_object* v_snd_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v_snd_1707_ = lean_ctor_get(v_a_1702_, 1);
lean_inc(v_snd_1707_);
lean_dec(v_a_1702_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_snd_1707_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1708_);
v___x_1710_ = v___x_1704_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
else
{
lean_object* v_val_1712_; lean_object* v___x_1714_; 
lean_inc_ref(v_fst_1706_);
lean_dec(v_a_1702_);
v_val_1712_ = lean_ctor_get(v_fst_1706_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v_fst_1706_, 1);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v_val_1712_);
v___x_1714_ = v___x_1704_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_val_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1701_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1701_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(lean_object* v_init_1725_, lean_object* v_ctx_1726_, uint8_t v_a_1727_, lean_object* v_as_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v_ctx_1726_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1731_);
return v___x_1744_;
}
else
{
lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1779_; 
v_snd_1745_ = lean_ctor_get(v_b_1731_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_b_1731_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_b_1731_, 0);
lean_dec(v_unused_1780_);
v___x_1747_ = v_b_1731_;
v_isShared_1748_ = v_isSharedCheck_1779_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_dec(v_b_1731_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1779_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_box(0);
v_a_1750_ = lean_array_uget_borrowed(v_as_1728_, v_i_1730_);
lean_inc(v_snd_1745_);
lean_inc_ref(v_ctx_1726_);
v___x_1751_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1725_, v_ctx_1726_, v_a_1727_, v_a_1750_, v_snd_1745_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1770_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1770_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1770_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
if (lean_obj_tag(v_a_1752_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec_ref(v_ctx_1726_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_a_1752_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1756_);
v___x_1758_ = v___x_1747_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_snd_1745_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1758_);
v___x_1760_ = v___x_1754_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; 
lean_del_object(v___x_1754_);
lean_dec(v_snd_1745_);
v_a_1763_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v_a_1752_, 1);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v_a_1763_);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1765_ = v___x_1747_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1763_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
size_t v___x_1766_; size_t v___x_1767_; 
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1730_, v___x_1766_);
v_i_1730_ = v___x_1767_;
v_b_1731_ = v___x_1765_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1747_);
lean_dec(v_snd_1745_);
lean_dec_ref(v_ctx_1726_);
v_a_1771_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1751_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1751_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(lean_object** _args){
lean_object* v_init_1781_ = _args[0];
lean_object* v_ctx_1782_ = _args[1];
lean_object* v_a_1783_ = _args[2];
lean_object* v_as_1784_ = _args[3];
lean_object* v_sz_1785_ = _args[4];
lean_object* v_i_1786_ = _args[5];
lean_object* v_b_1787_ = _args[6];
lean_object* v___y_1788_ = _args[7];
lean_object* v___y_1789_ = _args[8];
lean_object* v___y_1790_ = _args[9];
lean_object* v___y_1791_ = _args[10];
lean_object* v___y_1792_ = _args[11];
lean_object* v___y_1793_ = _args[12];
lean_object* v___y_1794_ = _args[13];
lean_object* v___y_1795_ = _args[14];
lean_object* v___y_1796_ = _args[15];
lean_object* v___y_1797_ = _args[16];
lean_object* v___y_1798_ = _args[17];
_start:
{
uint8_t v_a_163328__boxed_1799_; size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_a_163328__boxed_1799_ = lean_unbox(v_a_1783_);
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1785_);
lean_dec(v_sz_1785_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_1781_, v_ctx_1782_, v_a_163328__boxed_1799_, v_as_1784_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v_as_1784_);
lean_dec_ref(v_init_1781_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(lean_object* v_init_1803_, lean_object* v_ctx_1804_, lean_object* v_a_1805_, lean_object* v_n_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_a_163356__boxed_1819_; lean_object* v_res_1820_; 
v_a_163356__boxed_1819_ = lean_unbox(v_a_1805_);
v_res_1820_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1803_, v_ctx_1804_, v_a_163356__boxed_1819_, v_n_1806_, v_b_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v_n_1806_);
lean_dec_ref(v_init_1803_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_ctx_1821_, uint8_t v_a_1822_, lean_object* v_t_1823_, lean_object* v_init_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_root_1836_; lean_object* v_tail_1837_; lean_object* v___x_1838_; 
v_root_1836_ = lean_ctor_get(v_t_1823_, 0);
v_tail_1837_ = lean_ctor_get(v_t_1823_, 1);
lean_inc_ref(v_ctx_1821_);
lean_inc_ref(v_init_1824_);
v___x_1838_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_1824_, v_ctx_1821_, v_a_1822_, v_root_1836_, v_init_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec_ref(v_init_1824_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1875_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1875_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1875_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; 
lean_dec_ref(v_ctx_1821_);
v_a_1843_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v_a_1839_, 1);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_a_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; size_t v_sz_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
lean_del_object(v___x_1841_);
v_a_1847_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v_a_1839_, 1);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1847_);
v_sz_1850_ = lean_array_size(v_tail_1837_);
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_1821_, v_a_1822_, v_tail_1837_, v_sz_1850_, v___x_1851_, v___x_1849_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1866_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; 
v_fst_1857_ = lean_ctor_get(v_a_1853_, 0);
if (lean_obj_tag(v_fst_1857_) == 0)
{
lean_object* v_snd_1858_; lean_object* v___x_1860_; 
v_snd_1858_ = lean_ctor_get(v_a_1853_, 1);
lean_inc(v_snd_1858_);
lean_dec(v_a_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_snd_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_snd_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1864_; 
lean_inc_ref(v_fst_1857_);
lean_dec(v_a_1853_);
v_val_1862_ = lean_ctor_get(v_fst_1857_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_fst_1857_, 1);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_val_1862_);
v___x_1864_ = v___x_1855_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1852_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1852_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_ctx_1821_);
v_a_1876_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1838_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1838_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_ctx_1884_, lean_object* v_a_1885_, lean_object* v_t_1886_, lean_object* v_init_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
uint8_t v_a_163577__boxed_1899_; lean_object* v_res_1900_; 
v_a_163577__boxed_1899_ = lean_unbox(v_a_1885_);
v_res_1900_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_1884_, v_a_163577__boxed_1899_, v_t_1886_, v_init_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_t_1886_);
return v_res_1900_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5));
v___x_1906_ = l_Lean_Name_append(v___x_1905_, v___x_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(lean_object* v_as_1907_, size_t v_i_1908_, size_t v_stop_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_a_1923_; uint8_t v___x_1927_; 
v___x_1927_ = lean_usize_dec_eq(v_i_1908_, v_stop_1909_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_array_uget_borrowed(v_as_1907_, v_i_1908_);
v___x_1929_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_1928_, v___y_1911_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = lean_unbox(v_a_1930_);
lean_dec(v_a_1930_);
if (v___x_1931_ == 0)
{
if (lean_obj_tag(v___x_1928_) == 2)
{
lean_object* v_a_1932_; lean_object* v_b_1933_; lean_object* v_eq_1934_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_toCold_1990_; lean_object* v_options_1991_; uint8_t v_hasTrace_1992_; 
v_a_1932_ = lean_ctor_get(v___x_1928_, 0);
v_b_1933_ = lean_ctor_get(v___x_1928_, 1);
v_eq_1934_ = lean_ctor_get(v___x_1928_, 3);
v_toCold_1990_ = lean_ctor_get(v___y_1919_, 0);
v_options_1991_ = lean_ctor_get(v_toCold_1990_, 2);
v_hasTrace_1992_ = lean_ctor_get_uint8(v_options_1991_, sizeof(void*)*1);
if (v_hasTrace_1992_ == 0)
{
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
v___y_1967_ = v___y_1919_;
v___y_1968_ = v___y_1920_;
goto v___jp_1958_;
}
else
{
lean_object* v_inheritedTraceOptions_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_inheritedTraceOptions_1993_ = lean_ctor_get(v_toCold_1990_, 11);
v___x_1994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0));
v___x_1995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
v___x_1996_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1993_, v_options_1991_, v___x_1995_);
if (v___x_1996_ == 0)
{
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
v___y_1967_ = v___y_1919_;
v___y_1968_ = v___y_1920_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc_ref(v_eq_1934_);
v___x_1997_ = l_Lean_MessageData_ofExpr(v_eq_1934_);
v___x_1998_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1994_, v___x_1997_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref_known(v___x_1998_, 1);
v___y_1959_ = v___y_1911_;
v___y_1960_ = v___y_1912_;
v___y_1961_ = v___y_1913_;
v___y_1962_ = v___y_1914_;
v___y_1963_ = v___y_1915_;
v___y_1964_ = v___y_1916_;
v___y_1965_ = v___y_1917_;
v___y_1966_ = v___y_1918_;
v___y_1967_ = v___y_1919_;
v___y_1968_ = v___y_1920_;
goto v___jp_1958_;
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_b_1910_);
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
v___jp_1935_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1940_);
lean_inc(v___y_1944_);
lean_inc_ref(v_eq_1934_);
v___x_1948_ = lean_grind_internalize(v_eq_1934_, v___y_1946_, v___x_1947_, v___y_1944_, v___y_1940_, v___y_1936_, v___y_1941_, v___y_1943_, v___y_1945_, v___y_1939_, v___y_1942_, v___y_1938_, v___y_1937_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1949_; 
lean_dec_ref_known(v___x_1948_, 1);
lean_inc_ref(v___x_1928_);
v___x_1949_ = lean_array_push(v_b_1910_, v___x_1928_);
v_a_1923_ = v___x_1949_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_b_1910_);
v_a_1950_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1948_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1948_);
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
v___jp_1958_:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1932_, v___y_1959_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1933_, v___y_1959_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; uint8_t v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = lean_nat_dec_le(v_a_1970_, v_a_1972_);
if (v___x_1973_ == 0)
{
lean_dec(v_a_1972_);
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1967_;
v___y_1939_ = v___y_1965_;
v___y_1940_ = v___y_1960_;
v___y_1941_ = v___y_1962_;
v___y_1942_ = v___y_1966_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1959_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v_a_1970_;
goto v___jp_1935_;
}
else
{
lean_dec(v_a_1970_);
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1967_;
v___y_1939_ = v___y_1965_;
v___y_1940_ = v___y_1960_;
v___y_1941_ = v___y_1962_;
v___y_1942_ = v___y_1966_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1959_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v_a_1972_;
goto v___jp_1935_;
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v_a_1970_);
lean_dec_ref(v_b_1910_);
v_a_1974_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1971_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1971_);
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
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_b_1910_);
v_a_1982_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1969_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1969_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
else
{
v_a_1923_ = v_b_1910_;
goto v___jp_1922_;
}
}
else
{
v_a_1923_ = v_b_1910_;
goto v___jp_1922_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v_b_1910_);
v_a_2007_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1929_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1929_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_1910_);
return v___x_2015_;
}
v___jp_1922_:
{
size_t v___x_1924_; size_t v___x_1925_; 
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_add(v_i_1908_, v___x_1924_);
v_i_1908_ = v___x_1925_;
v_b_1910_ = v_a_1923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(lean_object* v_as_2016_, lean_object* v_i_2017_, lean_object* v_stop_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
size_t v_i_boxed_2031_; size_t v_stop_boxed_2032_; lean_object* v_res_2033_; 
v_i_boxed_2031_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_stop_boxed_2032_ = lean_unbox_usize(v_stop_2018_);
lean_dec(v_stop_2018_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2016_, v_i_boxed_2031_, v_stop_boxed_2032_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v_as_2016_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_2036_, lean_object* v_start_2037_, lean_object* v_stop_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0));
v___x_2051_ = lean_nat_dec_lt(v_start_2037_, v_stop_2038_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_array_get_size(v_as_2036_);
v___x_2054_ = lean_nat_dec_le(v_stop_2038_, v___x_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_nat_dec_lt(v_start_2037_, v___x_2053_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2050_);
return v___x_2056_;
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_usize_of_nat(v_start_2037_);
v___x_2058_ = lean_usize_of_nat(v___x_2053_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2036_, v___x_2057_, v___x_2058_, v___x_2050_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2059_;
}
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_usize_of_nat(v_start_2037_);
v___x_2061_ = lean_usize_of_nat(v_stop_2038_);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_2036_, v___x_2060_, v___x_2061_, v___x_2050_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_2063_, lean_object* v_start_2064_, lean_object* v_stop_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_2063_, v_start_2064_, v_stop_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v_stop_2065_);
lean_dec(v_start_2064_);
lean_dec_ref(v_as_2063_);
return v_res_2077_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_unsigned_to_nat(16u);
v___x_2080_ = lean_mk_array(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2095_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2306_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2306_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2306_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v_mbtc_2109_; 
v_mbtc_2109_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*14 + 18);
lean_dec(v_a_2105_);
if (v_mbtc_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
lean_dec_ref(v_ctx_2092_);
v___x_2110_ = lean_box(v_mbtc_2109_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2110_);
v___x_2112_ = v___x_2107_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
else
{
lean_object* v___x_2114_; 
lean_del_object(v___x_2107_);
v___x_2114_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2093_, v_a_2095_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2305_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2305_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2305_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_unbox(v_a_2115_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_toGoalState_2122_; lean_object* v_exprs_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; 
lean_del_object(v___x_2117_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_st_ref_get(v_a_2093_);
v_toGoalState_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc_ref(v_toGoalState_2122_);
lean_dec(v___x_2121_);
v_exprs_2123_ = lean_ctor_get(v_toGoalState_2122_, 2);
lean_inc_ref(v_exprs_2123_);
lean_dec_ref(v_toGoalState_2122_);
v___x_2124_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2125_ = lean_unbox(v_a_2115_);
v___x_2126_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(v_ctx_2092_, v___x_2125_, v_exprs_2123_, v___x_2124_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec_ref(v_exprs_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2291_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2291_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2291_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_snd_2131_; lean_object* v_size_2132_; lean_object* v_buckets_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2290_; 
v_snd_2131_ = lean_ctor_get(v_a_2127_, 1);
lean_inc(v_snd_2131_);
lean_dec(v_a_2127_);
v_size_2132_ = lean_ctor_get(v_snd_2131_, 0);
v_buckets_2133_ = lean_ctor_get(v_snd_2131_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_snd_2131_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2135_ = v_snd_2131_;
v_isShared_2136_ = v_isSharedCheck_2290_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_buckets_2133_);
lean_inc(v_size_2132_);
lean_dec(v_snd_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2290_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_nat_dec_eq(v_size_2132_, v___x_2120_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_del_object(v___x_2129_);
lean_dec(v_a_2115_);
v___x_2138_ = lean_st_ref_get(v_a_2093_);
v___x_2139_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2095_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_toGoalState_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2277_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v_toGoalState_2141_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v___x_2138_, 1);
lean_dec(v_unused_2278_);
v___x_2143_ = v___x_2138_;
v_isShared_2144_ = v_isSharedCheck_2277_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_toGoalState_2141_);
lean_dec(v___x_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2277_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_split_2145_; lean_object* v_splits_2146_; lean_object* v_num_2147_; uint8_t v___x_2148_; lean_object* v___y_2150_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2206_; 
v_split_2145_ = lean_ctor_get(v_toGoalState_2141_, 14);
lean_inc_ref(v_split_2145_);
lean_dec_ref(v_toGoalState_2141_);
v_splits_2146_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_splits_2146_);
lean_dec(v_a_2140_);
v_num_2147_ = lean_ctor_get(v_split_2145_, 0);
lean_inc(v_num_2147_);
lean_dec_ref(v_split_2145_);
v___x_2148_ = lean_nat_dec_lt(v_splits_2146_, v_num_2147_);
lean_dec(v_num_2147_);
lean_dec(v_splits_2146_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
lean_del_object(v___x_2143_);
lean_del_object(v___x_2135_);
v___x_2212_ = lean_mk_empty_array_with_capacity(v_size_2132_);
lean_dec(v_size_2132_);
v___x_2213_ = lean_array_get_size(v_buckets_2133_);
v___x_2214_ = lean_nat_dec_lt(v___x_2120_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_dec_ref(v_buckets_2133_);
v___y_2206_ = v___x_2212_;
goto v___jp_2205_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2213_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_2133_, v___x_2215_, v___x_2216_, v___x_2212_);
lean_dec_ref(v_buckets_2133_);
v___y_2206_ = v___x_2217_;
goto v___jp_2205_;
}
}
else
{
lean_object* v___x_2218_; 
lean_dec_ref(v_buckets_2133_);
lean_dec(v_size_2132_);
v___x_2218_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2095_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v_splits_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v_splits_2220_ = lean_ctor_get(v_a_2219_, 0);
lean_inc(v_splits_2220_);
lean_dec(v_a_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2222_ = l_Nat_reprFast(v_splits_2220_);
v___x_2223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = l_Lean_MessageData_ofFormat(v___x_2223_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 7);
lean_ctor_set(v___x_2143_, 1, v___x_2224_);
lean_ctor_set(v___x_2143_, 0, v___x_2221_);
v___x_2226_ = v___x_2143_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 7);
lean_ctor_set(v___x_2135_, 1, v___x_2227_);
lean_ctor_set(v___x_2135_, 0, v___x_2226_);
v___x_2229_ = v___x_2135_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2097_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2258_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2258_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2258_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v_verbose_2235_; 
v_verbose_2235_ = lean_ctor_get_uint8(v_a_2231_, 0);
lean_dec(v_a_2231_);
if (v_verbose_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_dec_ref(v___x_2229_);
v___x_2236_ = lean_box(v___x_2137_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2236_);
v___x_2238_ = v___x_2233_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
lean_object* v___x_2240_; 
lean_del_object(v___x_2233_);
v___x_2240_ = l_Lean_Meta_Sym_reportIssue(v___x_2229_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2248_; 
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2240_, 0);
lean_dec(v_unused_2249_);
v___x_2242_ = v___x_2240_;
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
else
{
lean_dec(v___x_2240_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = lean_box(v___x_2137_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2240_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2240_);
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
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec_ref(v___x_2229_);
v_a_2259_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2230_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2230_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_del_object(v___x_2143_);
lean_del_object(v___x_2135_);
v_a_2269_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2218_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2218_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
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
v___jp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_array_get_size(v___y_2150_);
v___x_2152_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(v___y_2150_, v___x_2120_, v___x_2151_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec_ref(v___y_2150_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2184_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2184_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2184_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_a_2153_);
v___x_2158_ = lean_nat_dec_eq(v___x_2157_, v___x_2120_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; size_t v_sz_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
lean_del_object(v___x_2155_);
v___x_2159_ = lean_box(0);
v_sz_2160_ = lean_array_size(v_a_2153_);
v___x_2161_ = ((size_t)0ULL);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_2153_, v_sz_2160_, v___x_2161_, v___x_2159_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2153_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2162_, 0);
lean_dec(v_unused_2171_);
v___x_2164_ = v___x_2162_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2162_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(v_mbtc_2109_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_a_2172_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec(v_a_2153_);
v___x_2180_ = lean_box(v___x_2148_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2180_);
v___x_2182_ = v___x_2155_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_a_2185_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2152_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2152_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
v___jp_2193_:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_2195_, v___y_2194_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec(v___y_2195_);
v___y_2150_ = v___x_2198_;
goto v___jp_2149_;
}
v___jp_2199_:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_nat_dec_le(v___y_2203_, v___y_2202_);
if (v___x_2204_ == 0)
{
lean_dec(v___y_2202_);
lean_inc(v___y_2203_);
v___y_2194_ = v___y_2200_;
v___y_2195_ = v___y_2201_;
v___y_2196_ = v___y_2203_;
v___y_2197_ = v___y_2203_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___y_2200_;
v___y_2195_ = v___y_2201_;
v___y_2196_ = v___y_2203_;
v___y_2197_ = v___y_2202_;
goto v___jp_2193_;
}
}
v___jp_2205_:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_array_get_size(v___y_2206_);
v___x_2208_ = lean_nat_dec_eq(v___x_2207_, v___x_2120_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = lean_nat_sub(v___x_2207_, v___x_2209_);
v___x_2211_ = lean_nat_dec_le(v___x_2120_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_inc(v___x_2210_);
v___y_2200_ = v___y_2206_;
v___y_2201_ = v___x_2207_;
v___y_2202_ = v___x_2210_;
v___y_2203_ = v___x_2210_;
goto v___jp_2199_;
}
else
{
v___y_2200_ = v___y_2206_;
v___y_2201_ = v___x_2207_;
v___y_2202_ = v___x_2210_;
v___y_2203_ = v___x_2120_;
goto v___jp_2199_;
}
}
else
{
v___y_2150_ = v___y_2206_;
goto v___jp_2149_;
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v___x_2138_);
lean_del_object(v___x_2135_);
lean_dec_ref(v_buckets_2133_);
lean_dec(v_size_2132_);
v_a_2279_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2139_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2139_);
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
else
{
lean_object* v___x_2288_; 
lean_del_object(v___x_2135_);
lean_dec_ref(v_buckets_2133_);
lean_dec(v_size_2132_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v_a_2115_);
v___x_2288_ = v___x_2129_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2115_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_a_2115_);
v_a_2292_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2126_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2126_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_ctx_2092_);
v___x_2300_ = 0;
v___x_2301_ = lean_box(v___x_2300_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2301_);
v___x_2303_ = v___x_2117_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
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
else
{
lean_dec_ref(v_ctx_2092_);
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_ctx_2092_);
v_a_2307_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2104_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2104_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_Grind_mbtc(v_ctx_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec(v_a_2316_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2328_, lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2328_, v_msg_2329_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2342_, lean_object* v_msg_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2342_, v_msg_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2356_, lean_object* v_m_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2357_, v_a_2358_, v_b_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2361_, lean_object* v_m_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2362_, v_a_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_m_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2365_, v_m_2366_, v_a_2367_);
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_m_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_ctx_2369_, lean_object* v_val_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v_as_2373_, lean_object* v_as_x27_2374_, lean_object* v_b_2375_, lean_object* v_a_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_2369_, v_val_2370_, v___x_2371_, v___x_2372_, v_as_x27_2374_, v_b_2375_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object** _args){
lean_object* v_ctx_2389_ = _args[0];
lean_object* v_val_2390_ = _args[1];
lean_object* v___x_2391_ = _args[2];
lean_object* v___x_2392_ = _args[3];
lean_object* v_as_2393_ = _args[4];
lean_object* v_as_x27_2394_ = _args[5];
lean_object* v_b_2395_ = _args[6];
lean_object* v_a_2396_ = _args[7];
lean_object* v___y_2397_ = _args[8];
lean_object* v___y_2398_ = _args[9];
lean_object* v___y_2399_ = _args[10];
lean_object* v___y_2400_ = _args[11];
lean_object* v___y_2401_ = _args[12];
lean_object* v___y_2402_ = _args[13];
lean_object* v___y_2403_ = _args[14];
lean_object* v___y_2404_ = _args[15];
lean_object* v___y_2405_ = _args[16];
lean_object* v___y_2406_ = _args[17];
lean_object* v___y_2407_ = _args[18];
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(v_ctx_2389_, v_val_2390_, v___x_2391_, v___x_2392_, v_as_2393_, v_as_x27_2394_, v_b_2395_, v_a_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec(v_as_x27_2394_);
lean_dec(v_as_2393_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_00_u03b2_2409_, lean_object* v_m_2410_, lean_object* v_a_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_m_2410_, v_a_2411_, v_b_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_n_2414_, lean_object* v_as_2415_, lean_object* v_lo_2416_, lean_object* v_hi_2417_, lean_object* v_w_2418_, lean_object* v_hlo_2419_, lean_object* v_hhi_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2414_, v_as_2415_, v_lo_2416_, v_hi_2417_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_n_2422_, lean_object* v_as_2423_, lean_object* v_lo_2424_, lean_object* v_hi_2425_, lean_object* v_w_2426_, lean_object* v_hlo_2427_, lean_object* v_hhi_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_2422_, v_as_2423_, v_lo_2424_, v_hi_2425_, v_w_2426_, v_hlo_2427_, v_hhi_2428_);
lean_dec(v_hi_2425_);
lean_dec(v_n_2422_);
return v_res_2429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2430_, lean_object* v_a_2431_, lean_object* v_x_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2431_, v_x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2434_, lean_object* v_a_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2434_, v_a_2435_, v_x_2436_);
lean_dec(v_x_2436_);
lean_dec_ref(v_a_2435_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2439_, lean_object* v_data_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2442_, lean_object* v_a_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2443_, v_x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2446_, lean_object* v_a_2447_, lean_object* v_x_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2446_, v_a_2447_, v_x_2448_);
lean_dec(v_x_2448_);
lean_dec_ref(v_a_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(lean_object* v_00_u03b2_2450_, lean_object* v_a_2451_, lean_object* v_x_2452_){
_start:
{
uint8_t v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_2451_, v_x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2454_, lean_object* v_a_2455_, lean_object* v_x_2456_){
_start:
{
uint8_t v_res_2457_; lean_object* v_r_2458_; 
v_res_2457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_2454_, v_a_2455_, v_x_2456_);
lean_dec(v_x_2456_);
lean_dec_ref(v_a_2455_);
v_r_2458_ = lean_box(v_res_2457_);
return v_r_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(lean_object* v_00_u03b2_2459_, lean_object* v_data_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(lean_object* v_00_u03b2_2462_, lean_object* v_a_2463_, lean_object* v_b_2464_, lean_object* v_x_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_2463_, v_b_2464_, v_x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(lean_object* v_n_2467_, lean_object* v_lo_2468_, lean_object* v_hi_2469_, lean_object* v_hhi_2470_, lean_object* v_pivot_2471_, lean_object* v_as_2472_, lean_object* v_i_2473_, lean_object* v_k_2474_, lean_object* v_ilo_2475_, lean_object* v_ik_2476_, lean_object* v_w_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2469_, v_pivot_2471_, v_as_2472_, v_i_2473_, v_k_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(lean_object* v_n_2479_, lean_object* v_lo_2480_, lean_object* v_hi_2481_, lean_object* v_hhi_2482_, lean_object* v_pivot_2483_, lean_object* v_as_2484_, lean_object* v_i_2485_, lean_object* v_k_2486_, lean_object* v_ilo_2487_, lean_object* v_ik_2488_, lean_object* v_w_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_2479_, v_lo_2480_, v_hi_2481_, v_hhi_2482_, v_pivot_2483_, v_as_2484_, v_i_2485_, v_k_2486_, v_ilo_2487_, v_ik_2488_, v_w_2489_);
lean_dec_ref(v_pivot_2483_);
lean_dec(v_hi_2481_);
lean_dec(v_lo_2480_);
lean_dec(v_n_2479_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2491_, lean_object* v_i_2492_, lean_object* v_source_2493_, lean_object* v_target_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2492_, v_source_2493_, v_target_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_2496_, lean_object* v_i_2497_, lean_object* v_source_2498_, lean_object* v_target_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_2497_, v_source_2498_, v_target_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_2502_, v_x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(lean_object* v_00_u03b2_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_2506_, v_x_2507_);
return v___x_2508_;
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
