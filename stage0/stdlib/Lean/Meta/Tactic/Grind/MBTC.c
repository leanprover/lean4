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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_isKnownCaseSplit___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_SplitInfo_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_lt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_SplitInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__1_value),LEAN_SCALAR_PTR_LITERAL(241, 58, 101, 243, 41, 236, 253, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 200, 238, 83, 121, 101, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(lean_object* v_as_324_, lean_object* v_lo_325_, lean_object* v_hi_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_lt(v_lo_325_, v_hi_326_);
if (v___x_327_ == 0)
{
lean_dec(v_lo_325_);
return v_as_324_;
}
else
{
lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; uint8_t v___x_332_; 
v___f_328_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___closed__0));
lean_inc(v_lo_325_);
v___x_329_ = l_Array_qpartition___redArg(v_as_324_, v___f_328_, v_lo_325_, v_hi_326_);
v_fst_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v___x_329_);
v___x_332_ = lean_nat_dec_le(v_hi_326_, v_fst_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(v_snd_331_, v_lo_325_, v_fst_330_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_fst_330_, v___x_334_);
lean_dec(v_fst_330_);
v_as_324_ = v___x_333_;
v_lo_325_ = v___x_335_;
goto _start;
}
else
{
lean_dec(v_fst_330_);
lean_dec(v_lo_325_);
return v_snd_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg___boxed(lean_object* v_as_337_, lean_object* v_lo_338_, lean_object* v_hi_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(v_as_337_, v_lo_338_, v_hi_339_);
lean_dec(v_hi_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_as_341_, size_t v_sz_342_, size_t v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_lt(v_i_343_, v_sz_342_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_b_344_);
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_359_; 
v_a_358_ = lean_array_uget_borrowed(v_as_341_, v_i_343_);
lean_inc(v_a_358_);
v___x_359_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_358_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_360_; size_t v___x_361_; size_t v___x_362_; 
lean_dec_ref(v___x_359_);
v___x_360_ = lean_box(0);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_343_, v___x_361_);
v_i_343_ = v___x_362_;
v_b_344_ = v___x_360_;
goto _start;
}
else
{
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object* v_as_364_, lean_object* v_sz_365_, lean_object* v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
size_t v_sz_boxed_379_; size_t v_i_boxed_380_; lean_object* v_res_381_; 
v_sz_boxed_379_ = lean_unbox_usize(v_sz_365_);
lean_dec(v_sz_365_);
v_i_boxed_380_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_as_364_, v_sz_boxed_379_, v_i_boxed_380_, v_b_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v_as_364_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
return v_x_382_;
}
else
{
lean_object* v_key_384_; lean_object* v_tail_385_; lean_object* v___x_386_; 
v_key_384_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_key_384_);
v_tail_385_ = lean_ctor_get(v_x_383_, 2);
lean_inc(v_tail_385_);
lean_dec_ref(v_x_383_);
v___x_386_ = lean_array_push(v_x_382_, v_key_384_);
v_x_382_ = v___x_386_;
v_x_383_ = v_tail_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* v_as_388_, size_t v_i_389_, size_t v_stop_390_, lean_object* v_b_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_389_, v_stop_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; size_t v___x_395_; size_t v___x_396_; 
v___x_393_ = lean_array_uget_borrowed(v_as_388_, v_i_389_);
lean_inc(v___x_393_);
v___x_394_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__10(v_b_391_, v___x_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_389_, v___x_395_);
v_i_389_ = v___x_396_;
v_b_391_ = v___x_394_;
goto _start;
}
else
{
return v_b_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11___boxed(lean_object* v_as_398_, lean_object* v_i_399_, lean_object* v_stop_400_, lean_object* v_b_401_){
_start:
{
size_t v_i_boxed_402_; size_t v_stop_boxed_403_; lean_object* v_res_404_; 
v_i_boxed_402_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_403_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11(v_as_398_, v_i_boxed_402_, v_stop_boxed_403_, v_b_401_);
lean_dec_ref(v_as_398_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object* v_msgData_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_env_412_; lean_object* v___x_413_; lean_object* v_mctx_414_; lean_object* v_lctx_415_; lean_object* v_options_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_411_ = lean_st_ref_get(v___y_409_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_411_);
v___x_413_ = lean_st_ref_get(v___y_407_);
v_mctx_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_mctx_414_);
lean_dec(v___x_413_);
v_lctx_415_ = lean_ctor_get(v___y_406_, 2);
v_options_416_ = lean_ctor_get(v___y_408_, 2);
lean_inc_ref(v_options_416_);
lean_inc_ref(v_lctx_415_);
v___x_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_417_, 0, v_env_412_);
lean_ctor_set(v___x_417_, 1, v_mctx_414_);
lean_ctor_set(v___x_417_, 2, v_lctx_415_);
lean_ctor_set(v___x_417_, 3, v_options_416_);
v___x_418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_msgData_405_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object* v_msgData_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_427_; double v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_float_of_nat(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* v_cls_432_, lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_485_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 5);
v___x_440_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_485_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_485_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_485_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v_traceState_446_; lean_object* v_env_447_; lean_object* v_nextMacroScope_448_; lean_object* v_ngen_449_; lean_object* v_auxDeclNGen_450_; lean_object* v_cache_451_; lean_object* v_messages_452_; lean_object* v_infoState_453_; lean_object* v_snapshotTasks_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_484_; 
v___x_445_ = lean_st_ref_take(v___y_437_);
v_traceState_446_ = lean_ctor_get(v___x_445_, 4);
v_env_447_ = lean_ctor_get(v___x_445_, 0);
v_nextMacroScope_448_ = lean_ctor_get(v___x_445_, 1);
v_ngen_449_ = lean_ctor_get(v___x_445_, 2);
v_auxDeclNGen_450_ = lean_ctor_get(v___x_445_, 3);
v_cache_451_ = lean_ctor_get(v___x_445_, 5);
v_messages_452_ = lean_ctor_get(v___x_445_, 6);
v_infoState_453_ = lean_ctor_get(v___x_445_, 7);
v_snapshotTasks_454_ = lean_ctor_get(v___x_445_, 8);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_484_ == 0)
{
v___x_456_ = v___x_445_;
v_isShared_457_ = v_isSharedCheck_484_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_snapshotTasks_454_);
lean_inc(v_infoState_453_);
lean_inc(v_messages_452_);
lean_inc(v_cache_451_);
lean_inc(v_traceState_446_);
lean_inc(v_auxDeclNGen_450_);
lean_inc(v_ngen_449_);
lean_inc(v_nextMacroScope_448_);
lean_inc(v_env_447_);
lean_dec(v___x_445_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_484_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint64_t v_tid_458_; lean_object* v_traces_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_483_; 
v_tid_458_ = lean_ctor_get_uint64(v_traceState_446_, sizeof(void*)*1);
v_traces_459_ = lean_ctor_get(v_traceState_446_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_traceState_446_);
if (v_isSharedCheck_483_ == 0)
{
v___x_461_ = v_traceState_446_;
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_traces_459_);
lean_dec(v_traceState_446_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; double v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_465_ = 0;
v___x_466_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_467_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_467_, 0, v_cls_432_);
lean_ctor_set(v___x_467_, 1, v___x_463_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set_float(v___x_467_, sizeof(void*)*3, v___x_464_);
lean_ctor_set_float(v___x_467_, sizeof(void*)*3 + 8, v___x_464_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*3 + 16, v___x_465_);
v___x_468_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_469_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v_a_441_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
lean_inc(v_ref_439_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_439_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_PersistentArray_push___redArg(v_traces_459_, v___x_470_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_471_);
v___x_473_ = v___x_461_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_471_);
lean_ctor_set_uint64(v_reuseFailAlloc_482_, sizeof(void*)*1, v_tid_458_);
v___x_473_ = v_reuseFailAlloc_482_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 4, v___x_473_);
v___x_475_ = v___x_456_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_env_447_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_448_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_449_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_450_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_messages_452_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_infoState_453_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_snapshotTasks_454_);
v___x_475_ = v_reuseFailAlloc_481_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_st_ref_set(v___y_437_, v___x_475_);
v___x_477_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_477_);
v___x_479_ = v___x_443_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_486_, v_msg_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2));
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__4));
v___x_504_ = l_Lean_Name_append(v___x_503_, v___x_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_a_521_; uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
v___x_527_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_526_, v___y_509_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; uint8_t v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_unbox(v_a_528_);
lean_dec(v_a_528_);
if (v___x_529_ == 0)
{
if (lean_obj_tag(v___x_526_) == 2)
{
lean_object* v_a_530_; lean_object* v_b_531_; lean_object* v_eq_532_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v_options_588_; uint8_t v_hasTrace_589_; 
v_a_530_ = lean_ctor_get(v___x_526_, 0);
v_b_531_ = lean_ctor_get(v___x_526_, 1);
v_eq_532_ = lean_ctor_get(v___x_526_, 3);
v_options_588_ = lean_ctor_get(v___y_517_, 2);
v_hasTrace_589_ = lean_ctor_get_uint8(v_options_588_, sizeof(void*)*1);
if (v_hasTrace_589_ == 0)
{
v___y_557_ = v___y_509_;
v___y_558_ = v___y_510_;
v___y_559_ = v___y_511_;
v___y_560_ = v___y_512_;
v___y_561_ = v___y_513_;
v___y_562_ = v___y_514_;
v___y_563_ = v___y_515_;
v___y_564_ = v___y_516_;
v___y_565_ = v___y_517_;
v___y_566_ = v___y_518_;
goto v___jp_556_;
}
else
{
lean_object* v_inheritedTraceOptions_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_inheritedTraceOptions_590_ = lean_ctor_get(v___y_517_, 13);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__2));
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__5);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_590_, v_options_588_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_557_ = v___y_509_;
v___y_558_ = v___y_510_;
v___y_559_ = v___y_511_;
v___y_560_ = v___y_512_;
v___y_561_ = v___y_513_;
v___y_562_ = v___y_514_;
v___y_563_ = v___y_515_;
v___y_564_ = v___y_516_;
v___y_565_ = v___y_517_;
v___y_566_ = v___y_518_;
goto v___jp_556_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_inc_ref(v_eq_532_);
v___x_594_ = l_Lean_MessageData_ofExpr(v_eq_532_);
v___x_595_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_591_, v___x_594_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_dec_ref(v___x_595_);
v___y_557_ = v___y_509_;
v___y_558_ = v___y_510_;
v___y_559_ = v___y_511_;
v___y_560_ = v___y_512_;
v___y_561_ = v___y_513_;
v___y_562_ = v___y_514_;
v___y_563_ = v___y_515_;
v___y_564_ = v___y_516_;
v___y_565_ = v___y_517_;
v___y_566_ = v___y_518_;
goto v___jp_556_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_b_508_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
v___jp_533_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_box(0);
lean_inc(v___y_538_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_537_);
lean_inc_ref(v___y_543_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v_eq_532_);
v___x_546_ = lean_grind_internalize(v_eq_532_, v___y_544_, v___x_545_, v___y_534_, v___y_535_, v___y_542_, v___y_540_, v___y_543_, v___y_537_, v___y_536_, v___y_539_, v___y_541_, v___y_538_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
lean_dec_ref(v___x_546_);
lean_inc_ref(v___x_526_);
v___x_547_ = lean_array_push(v_b_508_, v___x_526_);
v_a_521_ = v___x_547_;
goto v___jp_520_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v_b_508_);
v_a_548_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_546_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
v___jp_556_:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_530_, v___y_557_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_531_, v___y_557_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v___x_571_ = lean_nat_dec_le(v_a_568_, v_a_570_);
if (v___x_571_ == 0)
{
lean_dec(v_a_570_);
v___y_534_ = v___y_557_;
v___y_535_ = v___y_558_;
v___y_536_ = v___y_563_;
v___y_537_ = v___y_562_;
v___y_538_ = v___y_566_;
v___y_539_ = v___y_564_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_565_;
v___y_542_ = v___y_559_;
v___y_543_ = v___y_561_;
v___y_544_ = v_a_568_;
goto v___jp_533_;
}
else
{
lean_dec(v_a_568_);
v___y_534_ = v___y_557_;
v___y_535_ = v___y_558_;
v___y_536_ = v___y_563_;
v___y_537_ = v___y_562_;
v___y_538_ = v___y_566_;
v___y_539_ = v___y_564_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_565_;
v___y_542_ = v___y_559_;
v___y_543_ = v___y_561_;
v___y_544_ = v_a_570_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_a_568_);
lean_dec_ref(v_b_508_);
v_a_572_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_569_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_569_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_b_508_);
v_a_580_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_567_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_567_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
v_a_521_ = v_b_508_;
goto v___jp_520_;
}
}
else
{
v_a_521_ = v_b_508_;
goto v___jp_520_;
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_b_508_);
v_a_604_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_527_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_527_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_b_508_);
return v___x_612_;
}
v___jp_520_:
{
size_t v___x_522_; size_t v___x_523_; 
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_506_, v___x_522_);
v_i_506_ = v___x_523_;
v_b_508_ = v_a_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___boxed(lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_stop_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; lean_object* v_res_630_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_615_);
lean_dec(v_stop_615_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(v_as_613_, v_i_boxed_628_, v_stop_boxed_629_, v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v_as_613_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_as_633_, lean_object* v_start_634_, lean_object* v_stop_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___closed__0));
v___x_648_ = lean_nat_dec_lt(v_start_634_, v_stop_635_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_array_get_size(v_as_633_);
v___x_651_ = lean_nat_dec_le(v_stop_635_, v___x_650_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_lt(v_start_634_, v___x_650_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_647_);
return v___x_653_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_usize_of_nat(v_start_634_);
v___x_655_ = lean_usize_of_nat(v___x_650_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(v_as_633_, v___x_654_, v___x_655_, v___x_647_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_656_;
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_usize_of_nat(v_start_634_);
v___x_658_ = lean_usize_of_nat(v_stop_635_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16(v_as_633_, v___x_657_, v___x_658_, v___x_647_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_as_660_, lean_object* v_start_661_, lean_object* v_stop_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7(v_as_660_, v_start_661_, v_stop_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec(v_stop_662_);
lean_dec(v_start_661_);
lean_dec_ref(v_as_660_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_box(0);
return v___x_677_;
}
else
{
lean_object* v_key_678_; lean_object* v_value_679_; lean_object* v_tail_680_; uint8_t v___x_681_; 
v_key_678_ = lean_ctor_get(v_x_676_, 0);
v_value_679_ = lean_ctor_get(v_x_676_, 1);
v_tail_680_ = lean_ctor_get(v_x_676_, 2);
v___x_681_ = lean_expr_eqv(v_key_678_, v_a_675_);
if (v___x_681_ == 0)
{
v_x_676_ = v_tail_680_;
goto _start;
}
else
{
lean_object* v___x_683_; 
lean_inc(v_value_679_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_value_679_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(lean_object* v_a_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec_ref(v_a_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* v_m_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_buckets_689_; lean_object* v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v_fold_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_buckets_689_ = lean_ctor_get(v_m_687_, 1);
v___x_690_ = lean_array_get_size(v_buckets_689_);
v___x_691_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_688_);
v___x_692_ = 32ULL;
v___x_693_ = lean_uint64_shift_right(v___x_691_, v___x_692_);
v_fold_694_ = lean_uint64_xor(v___x_691_, v___x_693_);
v___x_695_ = 16ULL;
v___x_696_ = lean_uint64_shift_right(v_fold_694_, v___x_695_);
v___x_697_ = lean_uint64_xor(v_fold_694_, v___x_696_);
v___x_698_ = lean_uint64_to_usize(v___x_697_);
v___x_699_ = lean_usize_of_nat(v___x_690_);
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_sub(v___x_699_, v___x_700_);
v___x_702_ = lean_usize_land(v___x_698_, v___x_701_);
v___x_703_ = lean_array_uget_borrowed(v_buckets_689_, v___x_702_);
v___x_704_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_688_, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_705_, v_a_706_);
lean_dec_ref(v_a_706_);
lean_dec_ref(v_m_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10___redArg(lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_dec(v_b_709_);
lean_dec_ref(v_a_708_);
return v_x_710_;
}
else
{
lean_object* v_key_711_; lean_object* v_value_712_; lean_object* v_tail_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_725_; 
v_key_711_ = lean_ctor_get(v_x_710_, 0);
v_value_712_ = lean_ctor_get(v_x_710_, 1);
v_tail_713_ = lean_ctor_get(v_x_710_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_725_ == 0)
{
v___x_715_ = v_x_710_;
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_tail_713_);
lean_inc(v_value_712_);
lean_inc(v_key_711_);
lean_dec(v_x_710_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = lean_expr_eqv(v_key_711_, v_a_708_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10___redArg(v_a_708_, v_b_709_, v_tail_713_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 2, v___x_718_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_key_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_value_712_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v_value_712_);
lean_dec(v_key_711_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_b_709_);
lean_ctor_set(v___x_715_, 0, v_a_708_);
v___x_723_ = v___x_715_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_708_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_b_709_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_tail_713_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg(lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
uint8_t v___x_728_; 
v___x_728_ = 0;
return v___x_728_;
}
else
{
lean_object* v_key_729_; lean_object* v_tail_730_; uint8_t v___x_731_; 
v_key_729_ = lean_ctor_get(v_x_727_, 0);
v_tail_730_ = lean_ctor_get(v_x_727_, 2);
v___x_731_ = lean_expr_eqv(v_key_729_, v_a_726_);
if (v___x_731_ == 0)
{
v_x_727_ = v_tail_730_;
goto _start;
}
else
{
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg___boxed(lean_object* v_a_733_, lean_object* v_x_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg(v_a_733_, v_x_734_);
lean_dec(v_x_734_);
lean_dec_ref(v_a_733_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20___redArg(lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 0)
{
return v_x_737_;
}
else
{
lean_object* v_key_739_; lean_object* v_value_740_; lean_object* v_tail_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_764_; 
v_key_739_ = lean_ctor_get(v_x_738_, 0);
v_value_740_ = lean_ctor_get(v_x_738_, 1);
v_tail_741_ = lean_ctor_get(v_x_738_, 2);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_738_);
if (v_isSharedCheck_764_ == 0)
{
v___x_743_ = v_x_738_;
v_isShared_744_ = v_isSharedCheck_764_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_tail_741_);
lean_inc(v_value_740_);
lean_inc(v_key_739_);
lean_dec(v_x_738_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_764_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v_fold_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; size_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_745_ = lean_array_get_size(v_x_737_);
v___x_746_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_key_739_);
v___x_747_ = 32ULL;
v___x_748_ = lean_uint64_shift_right(v___x_746_, v___x_747_);
v_fold_749_ = lean_uint64_xor(v___x_746_, v___x_748_);
v___x_750_ = 16ULL;
v___x_751_ = lean_uint64_shift_right(v_fold_749_, v___x_750_);
v___x_752_ = lean_uint64_xor(v_fold_749_, v___x_751_);
v___x_753_ = lean_uint64_to_usize(v___x_752_);
v___x_754_ = lean_usize_of_nat(v___x_745_);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_sub(v___x_754_, v___x_755_);
v___x_757_ = lean_usize_land(v___x_753_, v___x_756_);
v___x_758_ = lean_array_uget_borrowed(v_x_737_, v___x_757_);
lean_inc(v___x_758_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 2, v___x_758_);
v___x_760_ = v___x_743_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_key_739_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_value_740_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_758_);
v___x_760_ = v_reuseFailAlloc_763_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_array_uset(v_x_737_, v___x_757_, v___x_760_);
v_x_737_ = v___x_761_;
v_x_738_ = v_tail_741_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11___redArg(lean_object* v_i_765_, lean_object* v_source_766_, lean_object* v_target_767_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_array_get_size(v_source_766_);
v___x_769_ = lean_nat_dec_lt(v_i_765_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v_source_766_);
lean_dec(v_i_765_);
return v_target_767_;
}
else
{
lean_object* v_es_770_; lean_object* v___x_771_; lean_object* v_source_772_; lean_object* v_target_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_es_770_ = lean_array_fget(v_source_766_, v_i_765_);
v___x_771_ = lean_box(0);
v_source_772_ = lean_array_fset(v_source_766_, v_i_765_, v___x_771_);
v_target_773_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20___redArg(v_target_767_, v_es_770_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_i_765_, v___x_774_);
lean_dec(v_i_765_);
v_i_765_ = v___x_775_;
v_source_766_ = v_source_772_;
v_target_767_ = v_target_773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9___redArg(lean_object* v_data_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_nbuckets_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_778_ = lean_array_get_size(v_data_777_);
v___x_779_ = lean_unsigned_to_nat(2u);
v_nbuckets_780_ = lean_nat_mul(v___x_778_, v___x_779_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_box(0);
v___x_783_ = lean_mk_array(v_nbuckets_780_, v___x_782_);
v___x_784_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11___redArg(v___x_781_, v_data_777_, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(lean_object* v_m_785_, lean_object* v_a_786_, lean_object* v_b_787_){
_start:
{
lean_object* v_size_788_; lean_object* v_buckets_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_832_; 
v_size_788_ = lean_ctor_get(v_m_785_, 0);
v_buckets_789_ = lean_ctor_get(v_m_785_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_m_785_);
if (v_isSharedCheck_832_ == 0)
{
v___x_791_ = v_m_785_;
v_isShared_792_ = v_isSharedCheck_832_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_buckets_789_);
lean_inc(v_size_788_);
lean_dec(v_m_785_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_832_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v_bkt_806_; uint8_t v___x_807_; 
v___x_793_ = lean_array_get_size(v_buckets_789_);
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_786_);
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
v_bkt_806_ = lean_array_uget_borrowed(v_buckets_789_, v___x_805_);
v___x_807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg(v_a_786_, v_bkt_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v_size_x27_809_; lean_object* v___x_810_; lean_object* v_buckets_x27_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v_size_x27_809_ = lean_nat_add(v_size_788_, v___x_808_);
lean_dec(v_size_788_);
lean_inc(v_bkt_806_);
v___x_810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_810_, 0, v_a_786_);
lean_ctor_set(v___x_810_, 1, v_b_787_);
lean_ctor_set(v___x_810_, 2, v_bkt_806_);
v_buckets_x27_811_ = lean_array_uset(v_buckets_789_, v___x_805_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(4u);
v___x_813_ = lean_nat_mul(v_size_x27_809_, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(3u);
v___x_815_ = lean_nat_div(v___x_813_, v___x_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_array_get_size(v_buckets_x27_811_);
v___x_817_ = lean_nat_dec_le(v___x_815_, v___x_816_);
lean_dec(v___x_815_);
if (v___x_817_ == 0)
{
lean_object* v_val_818_; lean_object* v___x_820_; 
v_val_818_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9___redArg(v_buckets_x27_811_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v_val_818_);
lean_ctor_set(v___x_791_, 0, v_size_x27_809_);
v___x_820_ = v___x_791_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_size_x27_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_val_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_823_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v_buckets_x27_811_);
lean_ctor_set(v___x_791_, 0, v_size_x27_809_);
v___x_823_ = v___x_791_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_size_x27_809_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_buckets_x27_811_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v___x_825_; lean_object* v_buckets_x27_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_inc(v_bkt_806_);
v___x_825_ = lean_box(0);
v_buckets_x27_826_ = lean_array_uset(v_buckets_789_, v___x_805_, v___x_825_);
v___x_827_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10___redArg(v_a_786_, v_b_787_, v_bkt_806_);
v___x_828_ = lean_array_uset(v_buckets_x27_826_, v___x_805_, v___x_827_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_828_);
v___x_830_ = v___x_791_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_size_788_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0(lean_object* v_val_833_, lean_object* v_info_834_){
_start:
{
lean_object* v_arg_835_; uint8_t v___x_836_; 
v_arg_835_ = lean_ctor_get(v_info_834_, 0);
v___x_836_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_833_, v_arg_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0___boxed(lean_object* v_val_837_, lean_object* v_info_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0(v_val_837_, v_info_838_);
lean_dec_ref(v_info_838_);
lean_dec_ref(v_val_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
uint8_t v___x_843_; 
v___x_843_ = 0;
return v___x_843_;
}
else
{
lean_object* v_key_844_; lean_object* v_tail_845_; uint8_t v___x_846_; 
v_key_844_ = lean_ctor_get(v_x_842_, 0);
v_tail_845_ = lean_ctor_get(v_x_842_, 2);
v___x_846_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_844_, v_a_841_);
if (v___x_846_ == 0)
{
v_x_842_ = v_tail_845_;
goto _start;
}
else
{
return v___x_846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_848_, v_x_849_);
lean_dec(v_x_849_);
lean_dec_ref(v_a_848_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
return v_x_852_;
}
else
{
lean_object* v_key_854_; lean_object* v_value_855_; lean_object* v_tail_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_879_; 
v_key_854_ = lean_ctor_get(v_x_853_, 0);
v_value_855_ = lean_ctor_get(v_x_853_, 1);
v_tail_856_ = lean_ctor_get(v_x_853_, 2);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_879_ == 0)
{
v___x_858_ = v_x_853_;
v_isShared_859_ = v_isSharedCheck_879_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_tail_856_);
lean_inc(v_value_855_);
lean_inc(v_key_854_);
lean_dec(v_x_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_879_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v_fold_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_860_ = lean_array_get_size(v_x_852_);
v___x_861_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_854_);
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
v___x_873_ = lean_array_uget_borrowed(v_x_852_, v___x_872_);
lean_inc(v___x_873_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v___x_873_);
v___x_875_ = v___x_858_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_key_854_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_value_855_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v___x_873_);
v___x_875_ = v_reuseFailAlloc_878_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; 
v___x_876_ = lean_array_uset(v_x_852_, v___x_872_, v___x_875_);
v_x_852_ = v___x_876_;
v_x_853_ = v_tail_856_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(lean_object* v_i_880_, lean_object* v_source_881_, lean_object* v_target_882_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_get_size(v_source_881_);
v___x_884_ = lean_nat_dec_lt(v_i_880_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_source_881_);
lean_dec(v_i_880_);
return v_target_882_;
}
else
{
lean_object* v_es_885_; lean_object* v___x_886_; lean_object* v_source_887_; lean_object* v_target_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_es_885_ = lean_array_fget(v_source_881_, v_i_880_);
v___x_886_ = lean_box(0);
v_source_887_ = lean_array_fset(v_source_881_, v_i_880_, v___x_886_);
v_target_888_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15___redArg(v_target_882_, v_es_885_);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_add(v_i_880_, v___x_889_);
lean_dec(v_i_880_);
v_i_880_ = v___x_890_;
v_source_881_ = v_source_887_;
v_target_882_ = v_target_888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(lean_object* v_data_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_nbuckets_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_893_ = lean_array_get_size(v_data_892_);
v___x_894_ = lean_unsigned_to_nat(2u);
v_nbuckets_895_ = lean_nat_mul(v___x_893_, v___x_894_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_box(0);
v___x_898_ = lean_mk_array(v_nbuckets_895_, v___x_897_);
v___x_899_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_896_, v_data_892_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_size_903_; lean_object* v_buckets_904_; lean_object* v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v_bkt_918_; uint8_t v___x_919_; 
v_size_903_ = lean_ctor_get(v_m_900_, 0);
v_buckets_904_ = lean_ctor_get(v_m_900_, 1);
v___x_905_ = lean_array_get_size(v_buckets_904_);
v___x_906_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_901_);
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___x_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_905_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v_bkt_918_ = lean_array_uget_borrowed(v_buckets_904_, v___x_917_);
v___x_919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_901_, v_bkt_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_940_; 
lean_inc_ref(v_buckets_904_);
lean_inc(v_size_903_);
v_isSharedCheck_940_ = !lean_is_exclusive(v_m_900_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; lean_object* v_unused_942_; 
v_unused_941_ = lean_ctor_get(v_m_900_, 1);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v_m_900_, 0);
lean_dec(v_unused_942_);
v___x_921_ = v_m_900_;
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
else
{
lean_dec(v_m_900_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v_size_x27_924_; lean_object* v___x_925_; lean_object* v_buckets_x27_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v_size_x27_924_ = lean_nat_add(v_size_903_, v___x_923_);
lean_dec(v_size_903_);
lean_inc(v_bkt_918_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v_a_901_);
lean_ctor_set(v___x_925_, 1, v_b_902_);
lean_ctor_set(v___x_925_, 2, v_bkt_918_);
v_buckets_x27_926_ = lean_array_uset(v_buckets_904_, v___x_917_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(4u);
v___x_928_ = lean_nat_mul(v_size_x27_924_, v___x_927_);
v___x_929_ = lean_unsigned_to_nat(3u);
v___x_930_ = lean_nat_div(v___x_928_, v___x_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_array_get_size(v_buckets_x27_926_);
v___x_932_ = lean_nat_dec_le(v___x_930_, v___x_931_);
lean_dec(v___x_930_);
if (v___x_932_ == 0)
{
lean_object* v_val_933_; lean_object* v___x_935_; 
v_val_933_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_926_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_val_933_);
lean_ctor_set(v___x_921_, 0, v_size_x27_924_);
v___x_935_ = v___x_921_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_size_x27_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_val_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_938_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_buckets_x27_926_);
lean_ctor_set(v___x_921_, 0, v_size_x27_924_);
v___x_938_ = v___x_921_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_size_x27_924_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_buckets_x27_926_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_dec(v_b_902_);
lean_dec_ref(v_a_901_);
return v_m_900_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object* v_ctx_943_, lean_object* v_val_944_, lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v_as_x27_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
if (lean_obj_tag(v_as_x27_947_) == 0)
{
lean_object* v___x_960_; 
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
lean_dec_ref(v_val_944_);
lean_dec_ref(v_ctx_943_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_948_);
return v___x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v_eqAssignment_963_; lean_object* v_arg_964_; lean_object* v___x_965_; 
v_head_961_ = lean_ctor_get(v_as_x27_947_, 0);
lean_inc(v_head_961_);
v_tail_962_ = lean_ctor_get(v_as_x27_947_, 1);
lean_inc(v_tail_962_);
lean_dec_ref(v_as_x27_947_);
v_eqAssignment_963_ = lean_ctor_get(v_ctx_943_, 2);
v_arg_964_ = lean_ctor_get(v_head_961_, 0);
lean_inc_ref(v_eqAssignment_963_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v_arg_964_);
lean_inc_ref(v_val_944_);
v___x_965_ = lean_apply_13(v_eqAssignment_963_, v_val_944_, v_arg_964_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, lean_box(0));
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = lean_unbox(v_a_966_);
lean_dec(v_a_966_);
if (v___x_967_ == 0)
{
lean_dec(v_head_961_);
v_as_x27_947_ = v_tail_962_;
goto _start;
}
else
{
lean_object* v___x_969_; 
lean_inc_ref(v_arg_964_);
lean_inc_ref(v_val_944_);
v___x_969_ = l_Lean_Meta_Grind_hasSameType(v_val_944_, v_arg_964_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_971_ == 0)
{
lean_dec(v_head_961_);
v_as_x27_947_ = v_tail_962_;
goto _start;
}
else
{
lean_object* v___x_973_; 
lean_inc(v___x_946_);
lean_inc_ref(v___x_945_);
v___x_973_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_945_, v_head_961_, v___x_946_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = lean_box(0);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_948_, v_a_974_, v___x_975_);
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_976_;
goto _start;
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_tail_962_);
lean_dec_ref(v_b_948_);
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
lean_dec_ref(v_val_944_);
lean_dec_ref(v_ctx_943_);
v_a_978_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_973_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_973_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec_ref(v_b_948_);
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
lean_dec_ref(v_val_944_);
lean_dec_ref(v_ctx_943_);
v_a_986_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_969_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_969_);
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
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec_ref(v_b_948_);
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
lean_dec_ref(v_val_944_);
lean_dec_ref(v_ctx_943_);
v_a_994_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_965_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_965_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_ctx_1002_ = _args[0];
lean_object* v_val_1003_ = _args[1];
lean_object* v___x_1004_ = _args[2];
lean_object* v___x_1005_ = _args[3];
lean_object* v_as_x27_1006_ = _args[4];
lean_object* v_b_1007_ = _args[5];
lean_object* v___y_1008_ = _args[6];
lean_object* v___y_1009_ = _args[7];
lean_object* v___y_1010_ = _args[8];
lean_object* v___y_1011_ = _args[9];
lean_object* v___y_1012_ = _args[10];
lean_object* v___y_1013_ = _args[11];
lean_object* v___y_1014_ = _args[12];
lean_object* v___y_1015_ = _args[13];
lean_object* v___y_1016_ = _args[14];
lean_object* v___y_1017_ = _args[15];
lean_object* v___y_1018_ = _args[16];
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_ctx_1002_, v_val_1003_, v___x_1004_, v___x_1005_, v_as_x27_1006_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
return v_res_1019_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1));
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7_spec__16___closed__4));
v___x_1027_ = l_Lean_Name_append(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__3));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__5));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_e_1034_, lean_object* v_ctx_1035_, lean_object* v___x_1036_, lean_object* v_as_1037_, size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_a_1053_; uint8_t v___x_1057_; 
v___x_1057_ = lean_usize_dec_lt(v_i_1039_, v_sz_1038_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_ctx_1035_);
lean_dec_ref(v_e_1034_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_b_1040_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v_snd_1060_; lean_object* v_fst_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1172_; 
v___x_1059_ = lean_st_ref_get(v___y_1041_);
v_snd_1060_ = lean_ctor_get(v_b_1040_, 1);
v_fst_1061_ = lean_ctor_get(v_b_1040_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_b_1040_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1063_ = v_b_1040_;
v_isShared_1064_ = v_isSharedCheck_1172_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1060_);
lean_inc(v_fst_1061_);
lean_dec(v_b_1040_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1172_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1171_; 
v_fst_1065_ = lean_ctor_get(v_snd_1060_, 0);
v_snd_1066_ = lean_ctor_get(v_snd_1060_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_snd_1060_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1068_ = v_snd_1060_;
v_isShared_1069_ = v_isSharedCheck_1171_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_snd_1060_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1171_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_map_1071_; lean_object* v_candidates_1072_; lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_array_uget_borrowed(v_as_1037_, v_i_1039_);
v___x_1082_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_1059_, v_a_1081_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1168_; 
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1168_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1168_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_hasTheoryVar_1087_; lean_object* v___x_1088_; 
v_hasTheoryVar_1087_ = lean_ctor_get(v_ctx_1035_, 1);
lean_inc_ref(v_hasTheoryVar_1087_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc(v_val_1083_);
v___x_1088_ = lean_apply_12(v_hasTheoryVar_1087_, v_val_1083_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; uint8_t v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v___x_1088_);
v___x_1090_ = lean_unbox(v_a_1089_);
lean_dec(v_a_1089_);
if (v___x_1090_ == 0)
{
lean_del_object(v___x_1085_);
lean_dec(v_val_1083_);
v_map_1071_ = v_fst_1061_;
v_candidates_1072_ = v_fst_1065_;
goto v___jp_1070_;
}
else
{
lean_object* v_options_1091_; lean_object* v_inheritedTraceOptions_1092_; uint8_t v_hasTrace_1093_; lean_object* v___f_1094_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; 
v_options_1091_ = lean_ctor_get(v___y_1049_, 2);
v_inheritedTraceOptions_1092_ = lean_ctor_get(v___y_1049_, 13);
v_hasTrace_1093_ = lean_ctor_get_uint8(v_options_1091_, sizeof(void*)*1);
lean_inc(v_val_1083_);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1094_, 0, v_val_1083_);
if (v_hasTrace_1093_ == 0)
{
lean_del_object(v___x_1085_);
v___y_1096_ = v___y_1041_;
v___y_1097_ = v___y_1042_;
v___y_1098_ = v___y_1043_;
v___y_1099_ = v___y_1044_;
v___y_1100_ = v___y_1045_;
v___y_1101_ = v___y_1046_;
v___y_1102_ = v___y_1047_;
v___y_1103_ = v___y_1048_;
v___y_1104_ = v___y_1049_;
v___y_1105_ = v___y_1050_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__1));
v___x_1136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__2);
v___x_1137_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1092_, v_options_1091_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_del_object(v___x_1085_);
v___y_1096_ = v___y_1041_;
v___y_1097_ = v___y_1042_;
v___y_1098_ = v___y_1043_;
v___y_1099_ = v___y_1044_;
v___y_1100_ = v___y_1045_;
v___y_1101_ = v___y_1046_;
v___y_1102_ = v___y_1047_;
v___y_1103_ = v___y_1048_;
v___y_1104_ = v___y_1049_;
v___y_1105_ = v___y_1050_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_inc(v_val_1083_);
v___x_1138_ = l_Lean_MessageData_ofExpr(v_val_1083_);
v___x_1139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__4);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
lean_inc_ref(v___x_1036_);
v___x_1141_ = l_Lean_MessageData_ofExpr(v___x_1036_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___closed__6);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
lean_inc(v_snd_1066_);
v___x_1145_ = l_Nat_reprFast(v_snd_1066_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1145_);
v___x_1147_ = v___x_1085_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = l_Lean_MessageData_ofFormat(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1144_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1135_, v___x_1149_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_dec_ref(v___x_1150_);
v___y_1096_ = v___y_1041_;
v___y_1097_ = v___y_1042_;
v___y_1098_ = v___y_1043_;
v___y_1099_ = v___y_1044_;
v___y_1100_ = v___y_1045_;
v___y_1101_ = v___y_1046_;
v___y_1102_ = v___y_1047_;
v___y_1103_ = v___y_1048_;
v___y_1104_ = v___y_1049_;
v___y_1105_ = v___y_1050_;
goto v___jp_1095_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v___f_1094_);
lean_dec(v_val_1083_);
lean_del_object(v___x_1068_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_ctx_1035_);
lean_dec_ref(v_e_1034_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
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
}
}
v___jp_1095_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc_ref_n(v_e_1034_, 2);
lean_inc(v_val_1083_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_val_1083_);
lean_ctor_set(v___x_1106_, 1, v_e_1034_);
v___x_1107_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_1034_, v_snd_1066_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_1061_, v_a_1108_);
if (lean_obj_tag(v___x_1109_) == 1)
{
lean_object* v_val_1110_; uint8_t v___x_1111_; 
v_val_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_n(v_val_1110_, 2);
lean_dec_ref(v___x_1109_);
v___x_1111_ = l_List_any___redArg(v_val_1110_, v___f_1094_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_inc(v_val_1110_);
lean_inc(v_snd_1066_);
lean_inc_ref(v___x_1106_);
lean_inc_ref(v_ctx_1035_);
v___x_1112_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_ctx_1035_, v_val_1083_, v___x_1106_, v_snd_1066_, v_val_1110_, v_fst_1065_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1106_);
lean_ctor_set(v___x_1114_, 1, v_val_1110_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_fst_1061_, v_a_1108_, v___x_1114_);
v_map_1071_ = v___x_1115_;
v_candidates_1072_ = v_a_1113_;
goto v___jp_1070_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_val_1110_);
lean_dec(v_a_1108_);
lean_dec_ref(v___x_1106_);
lean_del_object(v___x_1068_);
lean_dec(v_snd_1066_);
lean_del_object(v___x_1063_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_ctx_1035_);
lean_dec_ref(v_e_1034_);
v_a_1116_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1112_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_dec(v_val_1110_);
lean_dec(v_a_1108_);
lean_dec_ref(v___x_1106_);
lean_dec(v_val_1083_);
v_map_1071_ = v_fst_1061_;
v_candidates_1072_ = v_fst_1065_;
goto v___jp_1070_;
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v___x_1109_);
lean_dec_ref(v___f_1094_);
lean_dec(v_val_1083_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1106_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_fst_1061_, v_a_1108_, v___x_1125_);
v_map_1071_ = v___x_1126_;
v_candidates_1072_ = v_fst_1065_;
goto v___jp_1070_;
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___f_1094_);
lean_dec(v_val_1083_);
lean_del_object(v___x_1068_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_ctx_1035_);
lean_dec_ref(v_e_1034_);
v_a_1127_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1107_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1107_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_del_object(v___x_1085_);
lean_dec(v_val_1083_);
lean_del_object(v___x_1068_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_ctx_1035_);
lean_dec_ref(v_e_1034_);
v_a_1160_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1088_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1088_);
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
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v___x_1082_);
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_fst_1065_);
lean_ctor_set(v___x_1169_, 1, v_snd_1066_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_fst_1061_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v_a_1053_ = v___x_1170_;
goto v___jp_1052_;
}
v___jp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_add(v_snd_1066_, v___x_1073_);
lean_dec(v_snd_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1074_);
lean_ctor_set(v___x_1068_, 0, v_candidates_1072_);
v___x_1076_ = v___x_1068_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_candidates_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1076_);
lean_ctor_set(v___x_1063_, 0, v_map_1071_);
v___x_1078_ = v___x_1063_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_map_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_a_1053_ = v___x_1078_;
goto v___jp_1052_;
}
}
}
}
}
}
v___jp_1052_:
{
size_t v___x_1054_; size_t v___x_1055_; 
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1039_, v___x_1054_);
v_i_1039_ = v___x_1055_;
v_b_1040_ = v_a_1053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5___boxed(lean_object** _args){
lean_object* v_e_1173_ = _args[0];
lean_object* v_ctx_1174_ = _args[1];
lean_object* v___x_1175_ = _args[2];
lean_object* v_as_1176_ = _args[3];
lean_object* v_sz_1177_ = _args[4];
lean_object* v_i_1178_ = _args[5];
lean_object* v_b_1179_ = _args[6];
lean_object* v___y_1180_ = _args[7];
lean_object* v___y_1181_ = _args[8];
lean_object* v___y_1182_ = _args[9];
lean_object* v___y_1183_ = _args[10];
lean_object* v___y_1184_ = _args[11];
lean_object* v___y_1185_ = _args[12];
lean_object* v___y_1186_ = _args[13];
lean_object* v___y_1187_ = _args[14];
lean_object* v___y_1188_ = _args[15];
lean_object* v___y_1189_ = _args[16];
lean_object* v___y_1190_ = _args[17];
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1177_);
lean_dec(v_sz_1177_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_e_1173_, v_ctx_1174_, v___x_1175_, v_as_1176_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v_as_1176_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25(lean_object* v_ctx_1194_, lean_object* v_as_1195_, size_t v_sz_1196_, size_t v_i_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_lt(v_i_1197_, v_sz_1196_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_ctx_1194_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_b_1198_);
return v___x_1211_;
}
else
{
lean_object* v_snd_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1313_; 
v_snd_1212_ = lean_ctor_get(v_b_1198_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_b_1198_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v_b_1198_, 0);
lean_dec(v_unused_1314_);
v___x_1214_ = v_b_1198_;
v_isShared_1215_ = v_isSharedCheck_1313_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snd_1212_);
lean_dec(v_b_1198_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1313_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1312_; 
v_fst_1216_ = lean_ctor_get(v_snd_1212_, 0);
v_snd_1217_ = lean_ctor_get(v_snd_1212_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_snd_1212_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1219_ = v_snd_1212_;
v_isShared_1220_ = v_isSharedCheck_1312_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snd_1217_);
lean_inc(v_fst_1216_);
lean_dec(v_snd_1212_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1312_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v_a_1223_; lean_object* v_a_1236_; uint8_t v___y_1238_; uint8_t v___x_1310_; 
v___x_1221_ = lean_box(0);
v_a_1236_ = lean_array_uget_borrowed(v_as_1195_, v_i_1197_);
v___x_1310_ = l_Lean_Expr_isApp(v_a_1236_);
if (v___x_1310_ == 0)
{
v___y_1238_ = v___x_1310_;
goto v___jp_1237_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Expr_isEq(v_a_1236_);
if (v___x_1311_ == 0)
{
v___y_1238_ = v___x_1310_;
goto v___jp_1237_;
}
else
{
goto v___jp_1230_;
}
}
v___jp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v_a_1223_);
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1225_ = v___x_1219_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_a_1223_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
size_t v___x_1226_; size_t v___x_1227_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1197_, v___x_1226_);
v_i_1197_ = v___x_1227_;
v_b_1198_ = v___x_1225_;
goto _start;
}
}
v___jp_1230_:
{
lean_object* v___x_1232_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_snd_1217_);
lean_ctor_set(v___x_1214_, 0, v_fst_1216_);
v___x_1232_ = v___x_1214_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_fst_1216_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_snd_1217_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
v_a_1223_ = v___x_1232_;
goto v___jp_1222_;
}
}
v___jp_1234_:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_fst_1216_);
lean_ctor_set(v___x_1235_, 1, v_snd_1217_);
v_a_1223_ = v___x_1235_;
goto v___jp_1222_;
}
v___jp_1237_:
{
if (v___y_1238_ == 0)
{
goto v___jp_1230_;
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Lean_Expr_isHEq(v_a_1236_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_del_object(v___x_1214_);
lean_inc(v_a_1236_);
v___x_1240_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1236_, v___y_1199_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; uint8_t v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_unbox(v_a_1241_);
lean_dec(v_a_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_fst_1216_);
lean_ctor_set(v___x_1243_, 1, v_snd_1217_);
v_a_1223_ = v___x_1243_;
goto v___jp_1222_;
}
else
{
lean_object* v_isInterpreted_1244_; lean_object* v___x_1245_; 
v_isInterpreted_1244_ = lean_ctor_get(v_ctx_1194_, 0);
lean_inc_ref(v_isInterpreted_1244_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc(v_a_1236_);
v___x_1245_ = lean_apply_12(v_isInterpreted_1244_, v_a_1236_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, lean_box(0));
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = l_Lean_Expr_getAppFn(v_a_1236_);
lean_inc_ref(v___x_1248_);
v___x_1249_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1248_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1249_);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1248_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v_dummy_1254_; lean_object* v_nargs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v_dummy_1254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1255_ = l_Lean_Expr_getAppNumArgs(v_a_1236_);
lean_inc(v_nargs_1255_);
v___x_1256_ = lean_mk_array(v_nargs_1255_, v_dummy_1254_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_sub(v_nargs_1255_, v___x_1257_);
lean_dec(v_nargs_1255_);
lean_inc_n(v_a_1236_, 2);
v___x_1259_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1236_, v___x_1256_, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_snd_1217_);
lean_ctor_set(v___x_1260_, 1, v___x_1253_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_fst_1216_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v_sz_1262_ = lean_array_size(v___x_1259_);
v___x_1263_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1194_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_a_1236_, v_ctx_1194_, v___x_1248_, v___x_1259_, v_sz_1262_, v___x_1263_, v___x_1261_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec_ref(v___x_1259_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v_snd_1266_; lean_object* v_fst_1267_; lean_object* v_fst_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v_snd_1266_ = lean_ctor_get(v_a_1265_, 1);
lean_inc(v_snd_1266_);
v_fst_1267_ = lean_ctor_get(v_a_1265_, 0);
lean_inc(v_fst_1267_);
lean_dec(v_a_1265_);
v_fst_1268_ = lean_ctor_get(v_snd_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_snd_1266_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_snd_1266_, 1);
lean_dec(v_unused_1276_);
v___x_1270_ = v_snd_1266_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_fst_1268_);
lean_dec(v_snd_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_fst_1268_);
lean_ctor_set(v___x_1270_, 0, v_fst_1267_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_fst_1267_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_fst_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_a_1223_ = v___x_1273_;
goto v___jp_1222_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1219_);
lean_dec_ref(v_ctx_1194_);
v_a_1277_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1264_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1264_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_dec_ref(v___x_1248_);
goto v___jp_1234_;
}
}
else
{
lean_dec_ref(v___x_1248_);
goto v___jp_1234_;
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___x_1248_);
lean_del_object(v___x_1219_);
lean_dec(v_snd_1217_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_ctx_1194_);
v_a_1285_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1249_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1249_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_fst_1216_);
lean_ctor_set(v___x_1293_, 1, v_snd_1217_);
v_a_1223_ = v___x_1293_;
goto v___jp_1222_;
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_del_object(v___x_1219_);
lean_dec(v_snd_1217_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_ctx_1194_);
v_a_1294_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1245_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1245_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_del_object(v___x_1219_);
lean_dec(v_snd_1217_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_ctx_1194_);
v_a_1302_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1240_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1240_);
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
goto v___jp_1230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25___boxed(lean_object* v_ctx_1315_, lean_object* v_as_1316_, lean_object* v_sz_1317_, lean_object* v_i_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
size_t v_sz_boxed_1331_; size_t v_i_boxed_1332_; lean_object* v_res_1333_; 
v_sz_boxed_1331_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_i_boxed_1332_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_res_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25(v_ctx_1315_, v_as_1316_, v_sz_boxed_1331_, v_i_boxed_1332_, v_b_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17(lean_object* v_ctx_1334_, lean_object* v_as_1335_, size_t v_sz_1336_, size_t v_i_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_lt(v_i_1337_, v_sz_1336_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref(v_ctx_1334_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_b_1338_);
return v___x_1351_;
}
else
{
lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1453_; 
v_snd_1352_ = lean_ctor_get(v_b_1338_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_b_1338_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_b_1338_, 0);
lean_dec(v_unused_1454_);
v___x_1354_ = v_b_1338_;
v_isShared_1355_ = v_isSharedCheck_1453_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_dec(v_b_1338_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1453_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1452_; 
v_fst_1356_ = lean_ctor_get(v_snd_1352_, 0);
v_snd_1357_ = lean_ctor_get(v_snd_1352_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_snd_1352_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1359_ = v_snd_1352_;
v_isShared_1360_ = v_isSharedCheck_1452_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_inc(v_fst_1356_);
lean_dec(v_snd_1352_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1452_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v_a_1363_; lean_object* v_a_1376_; uint8_t v___y_1378_; uint8_t v___x_1450_; 
v___x_1361_ = lean_box(0);
v_a_1376_ = lean_array_uget_borrowed(v_as_1335_, v_i_1337_);
v___x_1450_ = l_Lean_Expr_isApp(v_a_1376_);
if (v___x_1450_ == 0)
{
v___y_1378_ = v___x_1450_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_Expr_isEq(v_a_1376_);
if (v___x_1451_ == 0)
{
v___y_1378_ = v___x_1450_;
goto v___jp_1377_;
}
else
{
goto v___jp_1370_;
}
}
v___jp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_a_1363_);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1365_ = v___x_1359_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1363_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1337_, v___x_1366_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17_spec__25(v_ctx_1334_, v_as_1335_, v_sz_1336_, v___x_1367_, v___x_1365_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1368_;
}
}
v___jp_1370_:
{
lean_object* v___x_1372_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_snd_1357_);
lean_ctor_set(v___x_1354_, 0, v_fst_1356_);
v___x_1372_ = v___x_1354_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_fst_1356_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1357_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_a_1363_ = v___x_1372_;
goto v___jp_1362_;
}
}
v___jp_1374_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_fst_1356_);
lean_ctor_set(v___x_1375_, 1, v_snd_1357_);
v_a_1363_ = v___x_1375_;
goto v___jp_1362_;
}
v___jp_1377_:
{
if (v___y_1378_ == 0)
{
goto v___jp_1370_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Lean_Expr_isHEq(v_a_1376_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_del_object(v___x_1354_);
lean_inc(v_a_1376_);
v___x_1380_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1376_, v___y_1339_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; uint8_t v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_unbox(v_a_1381_);
lean_dec(v_a_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_fst_1356_);
lean_ctor_set(v___x_1383_, 1, v_snd_1357_);
v_a_1363_ = v___x_1383_;
goto v___jp_1362_;
}
else
{
lean_object* v_isInterpreted_1384_; lean_object* v___x_1385_; 
v_isInterpreted_1384_ = lean_ctor_get(v_ctx_1334_, 0);
lean_inc_ref(v_isInterpreted_1384_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc(v_a_1376_);
v___x_1385_ = lean_apply_12(v_isInterpreted_1384_, v_a_1376_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, lean_box(0));
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; uint8_t v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = l_Lean_Expr_getAppFn(v_a_1376_);
lean_inc_ref(v___x_1388_);
v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1388_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; uint8_t v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = lean_unbox(v_a_1390_);
lean_dec(v_a_1390_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1388_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v_dummy_1394_; lean_object* v_nargs_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; size_t v_sz_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v_dummy_1394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1395_ = l_Lean_Expr_getAppNumArgs(v_a_1376_);
lean_inc(v_nargs_1395_);
v___x_1396_ = lean_mk_array(v_nargs_1395_, v_dummy_1394_);
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_sub(v_nargs_1395_, v___x_1397_);
lean_dec(v_nargs_1395_);
lean_inc_n(v_a_1376_, 2);
v___x_1399_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1376_, v___x_1396_, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_snd_1357_);
lean_ctor_set(v___x_1400_, 1, v___x_1393_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_fst_1356_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v_sz_1402_ = lean_array_size(v___x_1399_);
v___x_1403_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1334_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_a_1376_, v_ctx_1334_, v___x_1388_, v___x_1399_, v_sz_1402_, v___x_1403_, v___x_1401_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___x_1399_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_snd_1406_; lean_object* v_fst_1407_; lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v_snd_1406_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1406_);
v_fst_1407_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1407_);
lean_dec(v_a_1405_);
v_fst_1408_ = lean_ctor_get(v_snd_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_snd_1406_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_snd_1406_, 1);
lean_dec(v_unused_1416_);
v___x_1410_ = v_snd_1406_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_fst_1408_);
lean_dec(v_snd_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_fst_1408_);
lean_ctor_set(v___x_1410_, 0, v_fst_1407_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_fst_1407_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_fst_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v_a_1363_ = v___x_1413_;
goto v___jp_1362_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1359_);
lean_dec_ref(v_ctx_1334_);
v_a_1417_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1404_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1404_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_dec_ref(v___x_1388_);
goto v___jp_1374_;
}
}
else
{
lean_dec_ref(v___x_1388_);
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___x_1388_);
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_fst_1356_);
lean_dec_ref(v_ctx_1334_);
v_a_1425_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1389_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1389_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_fst_1356_);
lean_ctor_set(v___x_1433_, 1, v_snd_1357_);
v_a_1363_ = v___x_1433_;
goto v___jp_1362_;
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_fst_1356_);
lean_dec_ref(v_ctx_1334_);
v_a_1434_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1385_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1385_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_fst_1356_);
lean_dec_ref(v_ctx_1334_);
v_a_1442_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1380_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1380_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
goto v___jp_1370_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17___boxed(lean_object* v_ctx_1455_, lean_object* v_as_1456_, lean_object* v_sz_1457_, lean_object* v_i_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
size_t v_sz_boxed_1471_; size_t v_i_boxed_1472_; lean_object* v_res_1473_; 
v_sz_boxed_1471_ = lean_unbox_usize(v_sz_1457_);
lean_dec(v_sz_1457_);
v_i_boxed_1472_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17(v_ctx_1455_, v_as_1456_, v_sz_boxed_1471_, v_i_boxed_1472_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v_as_1456_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(lean_object* v_init_1474_, lean_object* v_ctx_1475_, lean_object* v_n_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
if (lean_obj_tag(v_n_1476_) == 0)
{
lean_object* v_cs_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1523_; 
v_cs_1489_ = lean_ctor_get(v_n_1476_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_n_1476_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1491_ = v_n_1476_;
v_isShared_1492_ = v_isSharedCheck_1523_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_cs_1489_);
lean_dec(v_n_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1523_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_b_1477_);
v_sz_1495_ = lean_array_size(v_cs_1489_);
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16(v_init_1474_, v_ctx_1475_, v_cs_1489_, v_sz_1495_, v___x_1496_, v___x_1494_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_cs_1489_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1514_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1514_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1514_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_fst_1502_; 
v_fst_1502_ = lean_ctor_get(v_a_1498_, 0);
if (lean_obj_tag(v_fst_1502_) == 0)
{
lean_object* v_snd_1503_; lean_object* v___x_1505_; 
v_snd_1503_ = lean_ctor_get(v_a_1498_, 1);
lean_inc(v_snd_1503_);
lean_dec(v_a_1498_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 1);
lean_ctor_set(v___x_1491_, 0, v_snd_1503_);
v___x_1505_ = v___x_1491_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_snd_1503_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1505_);
v___x_1507_ = v___x_1500_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1512_; 
lean_inc_ref(v_fst_1502_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1491_);
v_val_1510_ = lean_ctor_get(v_fst_1502_, 0);
lean_inc(v_val_1510_);
lean_dec_ref(v_fst_1502_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_val_1510_);
v___x_1512_ = v___x_1500_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_val_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_del_object(v___x_1491_);
v_a_1515_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1497_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1497_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
else
{
lean_object* v_vs_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1558_; 
v_vs_1524_ = lean_ctor_get(v_n_1476_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_n_1476_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1526_ = v_n_1476_;
v_isShared_1527_ = v_isSharedCheck_1558_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_vs_1524_);
lean_dec(v_n_1476_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1558_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; size_t v_sz_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v_b_1477_);
v_sz_1530_ = lean_array_size(v_vs_1524_);
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__17(v_ctx_1475_, v_vs_1524_, v_sz_1530_, v___x_1531_, v___x_1529_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_vs_1524_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1549_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1549_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1549_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_fst_1537_; 
v_fst_1537_ = lean_ctor_get(v_a_1533_, 0);
if (lean_obj_tag(v_fst_1537_) == 0)
{
lean_object* v_snd_1538_; lean_object* v___x_1540_; 
v_snd_1538_ = lean_ctor_get(v_a_1533_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_a_1533_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_snd_1538_);
v___x_1540_ = v___x_1526_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_snd_1538_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1540_);
v___x_1542_ = v___x_1535_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; 
lean_inc_ref(v_fst_1537_);
lean_dec(v_a_1533_);
lean_del_object(v___x_1526_);
v_val_1545_ = lean_ctor_get(v_fst_1537_, 0);
lean_inc(v_val_1545_);
lean_dec_ref(v_fst_1537_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v_val_1545_);
v___x_1547_ = v___x_1535_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_val_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_del_object(v___x_1526_);
v_a_1550_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1532_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1532_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16(lean_object* v_init_1559_, lean_object* v_ctx_1560_, lean_object* v_as_1561_, size_t v_sz_1562_, size_t v_i_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_usize_dec_lt(v_i_1563_, v_sz_1562_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v_ctx_1560_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_b_1564_);
return v___x_1577_;
}
else
{
lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1612_; 
v_snd_1578_ = lean_ctor_get(v_b_1564_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_b_1564_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_b_1564_, 0);
lean_dec(v_unused_1613_);
v___x_1580_ = v_b_1564_;
v_isShared_1581_ = v_isSharedCheck_1612_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_dec(v_b_1564_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1612_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_array_uget_borrowed(v_as_1561_, v_i_1563_);
lean_inc(v_snd_1578_);
lean_inc(v_a_1582_);
lean_inc_ref(v_ctx_1560_);
v___x_1583_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(v_init_1559_, v_ctx_1560_, v_a_1582_, v_snd_1578_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1603_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
if (lean_obj_tag(v_a_1584_) == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec_ref(v_ctx_1560_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_a_1584_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1588_);
v___x_1590_ = v___x_1580_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_snd_1578_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1590_);
v___x_1592_ = v___x_1586_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_del_object(v___x_1586_);
lean_dec(v_snd_1578_);
v_a_1595_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v_a_1584_);
v___x_1596_ = lean_box(0);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_a_1595_);
lean_ctor_set(v___x_1580_, 0, v___x_1596_);
v___x_1598_ = v___x_1580_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1595_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
size_t v___x_1599_; size_t v___x_1600_; 
v___x_1599_ = ((size_t)1ULL);
v___x_1600_ = lean_usize_add(v_i_1563_, v___x_1599_);
v_i_1563_ = v___x_1600_;
v_b_1564_ = v___x_1598_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1580_);
lean_dec(v_snd_1578_);
lean_dec_ref(v_ctx_1560_);
v_a_1604_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1583_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1583_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16___boxed(lean_object** _args){
lean_object* v_init_1614_ = _args[0];
lean_object* v_ctx_1615_ = _args[1];
lean_object* v_as_1616_ = _args[2];
lean_object* v_sz_1617_ = _args[3];
lean_object* v_i_1618_ = _args[4];
lean_object* v_b_1619_ = _args[5];
lean_object* v___y_1620_ = _args[6];
lean_object* v___y_1621_ = _args[7];
lean_object* v___y_1622_ = _args[8];
lean_object* v___y_1623_ = _args[9];
lean_object* v___y_1624_ = _args[10];
lean_object* v___y_1625_ = _args[11];
lean_object* v___y_1626_ = _args[12];
lean_object* v___y_1627_ = _args[13];
lean_object* v___y_1628_ = _args[14];
lean_object* v___y_1629_ = _args[15];
lean_object* v___y_1630_ = _args[16];
_start:
{
size_t v_sz_boxed_1631_; size_t v_i_boxed_1632_; lean_object* v_res_1633_; 
v_sz_boxed_1631_ = lean_unbox_usize(v_sz_1617_);
lean_dec(v_sz_1617_);
v_i_boxed_1632_ = lean_unbox_usize(v_i_1618_);
lean_dec(v_i_1618_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13_spec__16(v_init_1614_, v_ctx_1615_, v_as_1616_, v_sz_boxed_1631_, v_i_boxed_1632_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v_as_1616_);
lean_dec_ref(v_init_1614_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13___boxed(lean_object* v_init_1634_, lean_object* v_ctx_1635_, lean_object* v_n_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(v_init_1634_, v_ctx_1635_, v_n_1636_, v_b_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v_init_1634_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19(lean_object* v_ctx_1650_, lean_object* v_as_1651_, size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_ctx_1650_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_b_1654_);
return v___x_1667_;
}
else
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1769_; 
v_snd_1668_ = lean_ctor_get(v_b_1654_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_b_1654_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_b_1654_, 0);
lean_dec(v_unused_1770_);
v___x_1670_ = v_b_1654_;
v_isShared_1671_ = v_isSharedCheck_1769_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v_b_1654_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1769_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_fst_1672_; lean_object* v_snd_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1768_; 
v_fst_1672_ = lean_ctor_get(v_snd_1668_, 0);
v_snd_1673_ = lean_ctor_get(v_snd_1668_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_snd_1668_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1675_ = v_snd_1668_;
v_isShared_1676_ = v_isSharedCheck_1768_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snd_1673_);
lean_inc(v_fst_1672_);
lean_dec(v_snd_1668_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1768_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v_a_1679_; lean_object* v_a_1692_; uint8_t v___y_1694_; uint8_t v___x_1766_; 
v___x_1677_ = lean_box(0);
v_a_1692_ = lean_array_uget_borrowed(v_as_1651_, v_i_1653_);
v___x_1766_ = l_Lean_Expr_isApp(v_a_1692_);
if (v___x_1766_ == 0)
{
v___y_1694_ = v___x_1766_;
goto v___jp_1693_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Lean_Expr_isEq(v_a_1692_);
if (v___x_1767_ == 0)
{
v___y_1694_ = v___x_1766_;
goto v___jp_1693_;
}
else
{
goto v___jp_1686_;
}
}
v___jp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v_a_1679_);
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1681_ = v___x_1675_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1679_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1653_, v___x_1682_);
v_i_1653_ = v___x_1683_;
v_b_1654_ = v___x_1681_;
goto _start;
}
}
v___jp_1686_:
{
lean_object* v___x_1688_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_snd_1673_);
lean_ctor_set(v___x_1670_, 0, v_fst_1672_);
v___x_1688_ = v___x_1670_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_fst_1672_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_snd_1673_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v_a_1679_ = v___x_1688_;
goto v___jp_1678_;
}
}
v___jp_1690_:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_fst_1672_);
lean_ctor_set(v___x_1691_, 1, v_snd_1673_);
v_a_1679_ = v___x_1691_;
goto v___jp_1678_;
}
v___jp_1693_:
{
if (v___y_1694_ == 0)
{
goto v___jp_1686_;
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = l_Lean_Expr_isHEq(v_a_1692_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
lean_del_object(v___x_1670_);
lean_inc(v_a_1692_);
v___x_1696_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1692_, v___y_1655_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; uint8_t v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = lean_unbox(v_a_1697_);
lean_dec(v_a_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_fst_1672_);
lean_ctor_set(v___x_1699_, 1, v_snd_1673_);
v_a_1679_ = v___x_1699_;
goto v___jp_1678_;
}
else
{
lean_object* v_isInterpreted_1700_; lean_object* v___x_1701_; 
v_isInterpreted_1700_ = lean_ctor_get(v_ctx_1650_, 0);
lean_inc_ref(v_isInterpreted_1700_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc(v_a_1692_);
v___x_1701_ = lean_apply_12(v_isInterpreted_1700_, v_a_1692_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, lean_box(0));
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = l_Lean_Expr_getAppFn(v_a_1692_);
lean_inc_ref(v___x_1704_);
v___x_1705_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1704_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1707_ == 0)
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1704_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v_dummy_1710_; lean_object* v_nargs_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; size_t v_sz_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1709_ = lean_unsigned_to_nat(0u);
v_dummy_1710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1711_ = l_Lean_Expr_getAppNumArgs(v_a_1692_);
lean_inc(v_nargs_1711_);
v___x_1712_ = lean_mk_array(v_nargs_1711_, v_dummy_1710_);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_sub(v_nargs_1711_, v___x_1713_);
lean_dec(v_nargs_1711_);
lean_inc_n(v_a_1692_, 2);
v___x_1715_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1692_, v___x_1712_, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_snd_1673_);
lean_ctor_set(v___x_1716_, 1, v___x_1709_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_fst_1672_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v_sz_1718_ = lean_array_size(v___x_1715_);
v___x_1719_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1650_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_a_1692_, v_ctx_1650_, v___x_1704_, v___x_1715_, v_sz_1718_, v___x_1719_, v___x_1717_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec_ref(v___x_1715_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_snd_1722_; lean_object* v_fst_1723_; lean_object* v_fst_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v_snd_1722_ = lean_ctor_get(v_a_1721_, 1);
lean_inc(v_snd_1722_);
v_fst_1723_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_fst_1723_);
lean_dec(v_a_1721_);
v_fst_1724_ = lean_ctor_get(v_snd_1722_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_snd_1722_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v_snd_1722_, 1);
lean_dec(v_unused_1732_);
v___x_1726_ = v_snd_1722_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_fst_1724_);
lean_dec(v_snd_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_fst_1724_);
lean_ctor_set(v___x_1726_, 0, v_fst_1723_);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_fst_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v_a_1679_ = v___x_1729_;
goto v___jp_1678_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_del_object(v___x_1675_);
lean_dec_ref(v_ctx_1650_);
v_a_1733_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1720_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1720_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
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
lean_dec_ref(v___x_1704_);
goto v___jp_1690_;
}
}
else
{
lean_dec_ref(v___x_1704_);
goto v___jp_1690_;
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v___x_1704_);
lean_del_object(v___x_1675_);
lean_dec(v_snd_1673_);
lean_dec(v_fst_1672_);
lean_dec_ref(v_ctx_1650_);
v_a_1741_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1705_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1705_);
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
else
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_fst_1672_);
lean_ctor_set(v___x_1749_, 1, v_snd_1673_);
v_a_1679_ = v___x_1749_;
goto v___jp_1678_;
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1675_);
lean_dec(v_snd_1673_);
lean_dec(v_fst_1672_);
lean_dec_ref(v_ctx_1650_);
v_a_1750_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1701_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1701_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1675_);
lean_dec(v_snd_1673_);
lean_dec(v_fst_1672_);
lean_dec_ref(v_ctx_1650_);
v_a_1758_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1696_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1696_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
goto v___jp_1686_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19___boxed(lean_object* v_ctx_1771_, lean_object* v_as_1772_, lean_object* v_sz_1773_, lean_object* v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
size_t v_sz_boxed_1787_; size_t v_i_boxed_1788_; lean_object* v_res_1789_; 
v_sz_boxed_1787_ = lean_unbox_usize(v_sz_1773_);
lean_dec(v_sz_1773_);
v_i_boxed_1788_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19(v_ctx_1771_, v_as_1772_, v_sz_boxed_1787_, v_i_boxed_1788_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_as_1772_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14(lean_object* v_ctx_1790_, lean_object* v_as_1791_, size_t v_sz_1792_, size_t v_i_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_lt(v_i_1793_, v_sz_1792_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_ctx_1790_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_b_1794_);
return v___x_1807_;
}
else
{
lean_object* v_snd_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1909_; 
v_snd_1808_ = lean_ctor_get(v_b_1794_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_b_1794_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; 
v_unused_1910_ = lean_ctor_get(v_b_1794_, 0);
lean_dec(v_unused_1910_);
v___x_1810_ = v_b_1794_;
v_isShared_1811_ = v_isSharedCheck_1909_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snd_1808_);
lean_dec(v_b_1794_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1909_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1908_; 
v_fst_1812_ = lean_ctor_get(v_snd_1808_, 0);
v_snd_1813_ = lean_ctor_get(v_snd_1808_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_snd_1808_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1815_ = v_snd_1808_;
v_isShared_1816_ = v_isSharedCheck_1908_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_snd_1813_);
lean_inc(v_fst_1812_);
lean_dec(v_snd_1808_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1908_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v_a_1819_; lean_object* v_a_1832_; uint8_t v___y_1834_; uint8_t v___x_1906_; 
v___x_1817_ = lean_box(0);
v_a_1832_ = lean_array_uget_borrowed(v_as_1791_, v_i_1793_);
v___x_1906_ = l_Lean_Expr_isApp(v_a_1832_);
if (v___x_1906_ == 0)
{
v___y_1834_ = v___x_1906_;
goto v___jp_1833_;
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_isEq(v_a_1832_);
if (v___x_1907_ == 0)
{
v___y_1834_ = v___x_1906_;
goto v___jp_1833_;
}
else
{
goto v___jp_1826_;
}
}
v___jp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v_a_1819_);
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1821_ = v___x_1815_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_a_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1793_, v___x_1822_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14_spec__19(v_ctx_1790_, v_as_1791_, v_sz_1792_, v___x_1823_, v___x_1821_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1824_;
}
}
v___jp_1826_:
{
lean_object* v___x_1828_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v_snd_1813_);
lean_ctor_set(v___x_1810_, 0, v_fst_1812_);
v___x_1828_ = v___x_1810_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1813_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v_a_1819_ = v___x_1828_;
goto v___jp_1818_;
}
}
v___jp_1830_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_fst_1812_);
lean_ctor_set(v___x_1831_, 1, v_snd_1813_);
v_a_1819_ = v___x_1831_;
goto v___jp_1818_;
}
v___jp_1833_:
{
if (v___y_1834_ == 0)
{
goto v___jp_1826_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_isHEq(v_a_1832_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_del_object(v___x_1810_);
lean_inc(v_a_1832_);
v___x_1836_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1832_, v___y_1795_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; uint8_t v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = lean_unbox(v_a_1837_);
lean_dec(v_a_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_fst_1812_);
lean_ctor_set(v___x_1839_, 1, v_snd_1813_);
v_a_1819_ = v___x_1839_;
goto v___jp_1818_;
}
else
{
lean_object* v_isInterpreted_1840_; lean_object* v___x_1841_; 
v_isInterpreted_1840_ = lean_ctor_get(v_ctx_1790_, 0);
lean_inc_ref(v_isInterpreted_1840_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1801_);
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc(v_a_1832_);
v___x_1841_ = lean_apply_12(v_isInterpreted_1840_, v_a_1832_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = lean_unbox(v_a_1842_);
lean_dec(v_a_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = l_Lean_Expr_getAppFn(v_a_1832_);
lean_inc_ref(v___x_1844_);
v___x_1845_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1844_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; uint8_t v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = lean_unbox(v_a_1846_);
lean_dec(v_a_1846_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v_dummy_1850_; lean_object* v_nargs_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; size_t v_sz_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1849_ = lean_unsigned_to_nat(0u);
v_dummy_1850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1851_ = l_Lean_Expr_getAppNumArgs(v_a_1832_);
lean_inc(v_nargs_1851_);
v___x_1852_ = lean_mk_array(v_nargs_1851_, v_dummy_1850_);
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_sub(v_nargs_1851_, v___x_1853_);
lean_dec(v_nargs_1851_);
lean_inc_n(v_a_1832_, 2);
v___x_1855_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1832_, v___x_1852_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_snd_1813_);
lean_ctor_set(v___x_1856_, 1, v___x_1849_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_fst_1812_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v_sz_1858_ = lean_array_size(v___x_1855_);
v___x_1859_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1790_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_a_1832_, v_ctx_1790_, v___x_1844_, v___x_1855_, v_sz_1858_, v___x_1859_, v___x_1857_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v___x_1855_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v_snd_1862_; lean_object* v_fst_1863_; lean_object* v_fst_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1860_);
v_snd_1862_ = lean_ctor_get(v_a_1861_, 1);
lean_inc(v_snd_1862_);
v_fst_1863_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_fst_1863_);
lean_dec(v_a_1861_);
v_fst_1864_ = lean_ctor_get(v_snd_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_snd_1862_, 1);
lean_dec(v_unused_1872_);
v___x_1866_ = v_snd_1862_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_fst_1864_);
lean_dec(v_snd_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v_fst_1864_);
lean_ctor_set(v___x_1866_, 0, v_fst_1863_);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1863_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_fst_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v_a_1819_ = v___x_1869_;
goto v___jp_1818_;
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_del_object(v___x_1815_);
lean_dec_ref(v_ctx_1790_);
v_a_1873_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1860_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1860_);
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
else
{
lean_dec_ref(v___x_1844_);
goto v___jp_1830_;
}
}
else
{
lean_dec_ref(v___x_1844_);
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v___x_1844_);
lean_del_object(v___x_1815_);
lean_dec(v_snd_1813_);
lean_dec(v_fst_1812_);
lean_dec_ref(v_ctx_1790_);
v_a_1881_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1845_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1845_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_fst_1812_);
lean_ctor_set(v___x_1889_, 1, v_snd_1813_);
v_a_1819_ = v___x_1889_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_del_object(v___x_1815_);
lean_dec(v_snd_1813_);
lean_dec(v_fst_1812_);
lean_dec_ref(v_ctx_1790_);
v_a_1890_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1841_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1841_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1815_);
lean_dec(v_snd_1813_);
lean_dec(v_fst_1812_);
lean_dec_ref(v_ctx_1790_);
v_a_1898_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1836_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1836_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
goto v___jp_1826_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14___boxed(lean_object* v_ctx_1911_, lean_object* v_as_1912_, lean_object* v_sz_1913_, lean_object* v_i_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
size_t v_sz_boxed_1927_; size_t v_i_boxed_1928_; lean_object* v_res_1929_; 
v_sz_boxed_1927_ = lean_unbox_usize(v_sz_1913_);
lean_dec(v_sz_1913_);
v_i_boxed_1928_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14(v_ctx_1911_, v_as_1912_, v_sz_boxed_1927_, v_i_boxed_1928_, v_b_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v_as_1912_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_ctx_1930_, lean_object* v_t_1931_, lean_object* v_init_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_root_1944_; lean_object* v_tail_1945_; lean_object* v___x_1946_; 
v_root_1944_ = lean_ctor_get(v_t_1931_, 0);
lean_inc_ref(v_root_1944_);
v_tail_1945_ = lean_ctor_get(v_t_1931_, 1);
lean_inc_ref(v_tail_1945_);
lean_dec_ref(v_t_1931_);
lean_inc_ref(v_ctx_1930_);
lean_inc_ref(v_init_1932_);
v___x_1946_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__13(v_init_1932_, v_ctx_1930_, v_root_1944_, v_init_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec_ref(v_init_1932_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1983_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1983_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1983_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
if (lean_obj_tag(v_a_1947_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; 
lean_dec_ref(v_tail_1945_);
lean_dec_ref(v_ctx_1930_);
v_a_1951_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v_a_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
lean_del_object(v___x_1949_);
v_a_1955_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v_a_1947_);
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_a_1955_);
v_sz_1958_ = lean_array_size(v_tail_1945_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6_spec__14(v_ctx_1930_, v_tail_1945_, v_sz_1958_, v___x_1959_, v___x_1957_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec_ref(v_tail_1945_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1974_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; 
v_fst_1965_ = lean_ctor_get(v_a_1961_, 0);
if (lean_obj_tag(v_fst_1965_) == 0)
{
lean_object* v_snd_1966_; lean_object* v___x_1968_; 
v_snd_1966_ = lean_ctor_get(v_a_1961_, 1);
lean_inc(v_snd_1966_);
lean_dec(v_a_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_snd_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_snd_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; 
lean_inc_ref(v_fst_1965_);
lean_dec(v_a_1961_);
v_val_1970_ = lean_ctor_get(v_fst_1965_, 0);
lean_inc(v_val_1970_);
lean_dec_ref(v_fst_1965_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_val_1970_);
v___x_1972_ = v___x_1963_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_val_1970_);
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
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1960_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1960_);
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
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_tail_1945_);
lean_dec_ref(v_ctx_1930_);
v_a_1984_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1946_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1946_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object* v_ctx_1992_, lean_object* v_t_1993_, lean_object* v_init_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6(v_ctx_1992_, v_t_1993_, v_init_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec(v___y_1995_);
return v_res_2006_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_unsigned_to_nat(16u);
v___x_2009_ = lean_mk_array(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v___x_2010_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
return v___x_2014_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__4(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__3));
v___x_2017_ = l_Lean_stringToMessageData(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__6(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__5));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2024_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2238_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2238_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2238_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
uint8_t v_mbtc_2038_; 
v_mbtc_2038_ = lean_ctor_get_uint8(v_a_2034_, sizeof(void*)*11 + 18);
lean_dec(v_a_2034_);
if (v_mbtc_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec_ref(v_ctx_2021_);
v___x_2039_ = lean_box(v_mbtc_2038_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2039_);
v___x_2041_ = v___x_2036_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
lean_object* v___x_2043_; 
lean_del_object(v___x_2036_);
v___x_2043_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2022_, v_a_2024_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2237_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2237_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2237_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_unbox(v_a_2044_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v_toGoalState_2050_; lean_object* v_exprs_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_del_object(v___x_2046_);
v___x_2049_ = lean_st_ref_get(v_a_2022_);
v_toGoalState_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_ref(v_toGoalState_2050_);
lean_dec(v___x_2049_);
v_exprs_2051_ = lean_ctor_get(v_toGoalState_2050_, 2);
lean_inc_ref(v_exprs_2051_);
lean_dec_ref(v_toGoalState_2050_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2054_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__6(v_ctx_2021_, v_exprs_2051_, v___x_2053_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2223_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2223_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2223_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_snd_2059_; lean_object* v_size_2060_; lean_object* v_buckets_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2222_; 
v_snd_2059_ = lean_ctor_get(v_a_2055_, 1);
lean_inc(v_snd_2059_);
lean_dec(v_a_2055_);
v_size_2060_ = lean_ctor_get(v_snd_2059_, 0);
v_buckets_2061_ = lean_ctor_get(v_snd_2059_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_snd_2059_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2063_ = v_snd_2059_;
v_isShared_2064_ = v_isSharedCheck_2222_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_buckets_2061_);
lean_inc(v_size_2060_);
lean_dec(v_snd_2059_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2222_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_nat_dec_eq(v_size_2060_, v___x_2052_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_del_object(v___x_2057_);
lean_dec(v_a_2044_);
v___x_2066_ = lean_st_ref_get(v_a_2022_);
v___x_2067_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2024_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___y_2070_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2126_; lean_object* v_toGoalState_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2209_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v_toGoalState_2132_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2066_, 1);
lean_dec(v_unused_2210_);
v___x_2134_ = v___x_2066_;
v_isShared_2135_ = v_isSharedCheck_2209_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_toGoalState_2132_);
lean_dec(v___x_2066_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2209_;
goto v_resetjp_2133_;
}
v___jp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_array_get_size(v___y_2070_);
v___x_2072_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__7(v___y_2070_, v___x_2052_, v___x_2071_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec_ref(v___y_2070_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2104_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2104_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2104_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_array_get_size(v_a_2073_);
v___x_2078_ = lean_nat_dec_eq(v___x_2077_, v___x_2052_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
lean_del_object(v___x_2075_);
v___x_2079_ = lean_box(0);
v_sz_2080_ = lean_array_size(v_a_2073_);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_a_2073_, v_sz_2080_, v___x_2081_, v___x_2079_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2073_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v___x_2082_, 0);
lean_dec(v_unused_2091_);
v___x_2084_ = v___x_2082_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v___x_2082_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_box(v_mbtc_2038_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_a_2092_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2082_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2082_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_a_2073_);
v___x_2100_ = lean_box(v___x_2065_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2100_);
v___x_2102_ = v___x_2075_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2072_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2072_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2118_; 
lean_dec(v___y_2114_);
v___x_2118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
v___y_2070_ = v___x_2118_;
goto v___jp_2069_;
}
v___jp_2119_:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_nat_dec_le(v___y_2123_, v___y_2122_);
if (v___x_2124_ == 0)
{
lean_dec(v___y_2122_);
lean_inc(v___y_2123_);
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v___y_2116_ = v___y_2123_;
v___y_2117_ = v___y_2123_;
goto v___jp_2113_;
}
else
{
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v___y_2116_ = v___y_2123_;
v___y_2117_ = v___y_2122_;
goto v___jp_2113_;
}
}
v___jp_2125_:
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = lean_array_get_size(v___y_2126_);
v___x_2128_ = lean_nat_dec_eq(v___x_2127_, v___x_2052_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(1u);
v___x_2130_ = lean_nat_sub(v___x_2127_, v___x_2129_);
v___x_2131_ = lean_nat_dec_le(v___x_2052_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_inc(v___x_2130_);
v___y_2120_ = v___x_2127_;
v___y_2121_ = v___y_2126_;
v___y_2122_ = v___x_2130_;
v___y_2123_ = v___x_2130_;
goto v___jp_2119_;
}
else
{
v___y_2120_ = v___x_2127_;
v___y_2121_ = v___y_2126_;
v___y_2122_ = v___x_2130_;
v___y_2123_ = v___x_2052_;
goto v___jp_2119_;
}
}
else
{
v___y_2070_ = v___y_2126_;
goto v___jp_2069_;
}
}
v_resetjp_2133_:
{
lean_object* v_split_2136_; lean_object* v_splits_2137_; lean_object* v_num_2138_; uint8_t v___x_2139_; 
v_split_2136_ = lean_ctor_get(v_toGoalState_2132_, 14);
lean_inc_ref(v_split_2136_);
lean_dec_ref(v_toGoalState_2132_);
v_splits_2137_ = lean_ctor_get(v_a_2068_, 0);
lean_inc(v_splits_2137_);
lean_dec(v_a_2068_);
v_num_2138_ = lean_ctor_get(v_split_2136_, 0);
lean_inc(v_num_2138_);
lean_dec_ref(v_split_2136_);
v___x_2139_ = lean_nat_dec_lt(v_splits_2137_, v_num_2138_);
lean_dec(v_num_2138_);
lean_dec(v_splits_2137_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
lean_del_object(v___x_2134_);
lean_del_object(v___x_2063_);
v___x_2140_ = lean_mk_empty_array_with_capacity(v_size_2060_);
lean_dec(v_size_2060_);
v___x_2141_ = lean_array_get_size(v_buckets_2061_);
v___x_2142_ = lean_nat_dec_lt(v___x_2052_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec_ref(v_buckets_2061_);
v___y_2126_ = v___x_2140_;
goto v___jp_2125_;
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___x_2141_, v___x_2141_);
if (v___x_2143_ == 0)
{
if (v___x_2142_ == 0)
{
lean_dec_ref(v_buckets_2061_);
v___y_2126_ = v___x_2140_;
goto v___jp_2125_;
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2141_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11(v_buckets_2061_, v___x_2144_, v___x_2145_, v___x_2140_);
lean_dec_ref(v_buckets_2061_);
v___y_2126_ = v___x_2146_;
goto v___jp_2125_;
}
}
else
{
size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = lean_usize_of_nat(v___x_2141_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__11(v_buckets_2061_, v___x_2147_, v___x_2148_, v___x_2140_);
lean_dec_ref(v_buckets_2061_);
v___y_2126_ = v___x_2149_;
goto v___jp_2125_;
}
}
}
else
{
lean_object* v___x_2150_; 
lean_dec_ref(v_buckets_2061_);
lean_dec(v_size_2060_);
v___x_2150_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2024_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2026_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2192_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2192_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2192_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_unbox(v_a_2153_);
lean_dec(v_a_2153_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_a_2151_);
lean_del_object(v___x_2134_);
lean_del_object(v___x_2063_);
v___x_2158_ = lean_box(v___x_2065_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2158_);
v___x_2160_ = v___x_2155_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v_splits_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_del_object(v___x_2155_);
v_splits_2162_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_splits_2162_);
lean_dec(v_a_2151_);
v___x_2163_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__4, &l_Lean_Meta_Grind_mbtc___closed__4_once, _init_l_Lean_Meta_Grind_mbtc___closed__4);
v___x_2164_ = l_Nat_reprFast(v_splits_2162_);
v___x_2165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = l_Lean_MessageData_ofFormat(v___x_2165_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 7);
lean_ctor_set(v___x_2134_, 1, v___x_2166_);
lean_ctor_set(v___x_2134_, 0, v___x_2163_);
v___x_2168_ = v___x_2134_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__6, &l_Lean_Meta_Grind_mbtc___closed__6_once, _init_l_Lean_Meta_Grind_mbtc___closed__6);
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 7);
lean_ctor_set(v___x_2063_, 1, v___x_2169_);
lean_ctor_set(v___x_2063_, 0, v___x_2168_);
v___x_2171_ = v___x_2063_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_Sym_reportIssue(v___x_2171_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2180_; 
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2172_, 0);
lean_dec(v_unused_2181_);
v___x_2174_ = v___x_2172_;
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v___x_2172_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = lean_box(v___x_2065_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2172_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2172_);
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
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_a_2151_);
lean_del_object(v___x_2134_);
lean_del_object(v___x_2063_);
v_a_2193_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2152_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2152_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_del_object(v___x_2134_);
lean_del_object(v___x_2063_);
v_a_2201_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2150_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2150_);
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
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v___x_2066_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_buckets_2061_);
lean_dec(v_size_2060_);
v_a_2211_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2067_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2067_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_del_object(v___x_2063_);
lean_dec_ref(v_buckets_2061_);
lean_dec(v_size_2060_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_a_2044_);
v___x_2220_ = v___x_2057_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2044_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2044_);
v_a_2224_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2054_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2054_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_dec(v_a_2044_);
lean_dec_ref(v_ctx_2021_);
v___x_2232_ = 0;
v___x_2233_ = lean_box(v___x_2232_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2233_);
v___x_2235_ = v___x_2046_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
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
lean_dec_ref(v_ctx_2021_);
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_ctx_2021_);
v_a_2239_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2033_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2033_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Meta_Grind_mbtc(v_ctx_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec(v_a_2248_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2260_, lean_object* v_msg_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2260_, v_msg_2261_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2274_, lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2274_, v_msg_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec(v___y_2276_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2288_, lean_object* v_m_2289_, lean_object* v_a_2290_, lean_object* v_b_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2289_, v_a_2290_, v_b_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2293_, lean_object* v_m_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2294_, v_a_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2297_, lean_object* v_m_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2297_, v_m_2298_, v_a_2299_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v_m_2298_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_ctx_2301_, lean_object* v_val_2302_, lean_object* v___x_2303_, lean_object* v___x_2304_, lean_object* v_as_2305_, lean_object* v_as_x27_2306_, lean_object* v_b_2307_, lean_object* v_a_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_ctx_2301_, v_val_2302_, v___x_2303_, v___x_2304_, v_as_x27_2306_, v_b_2307_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object** _args){
lean_object* v_ctx_2321_ = _args[0];
lean_object* v_val_2322_ = _args[1];
lean_object* v___x_2323_ = _args[2];
lean_object* v___x_2324_ = _args[3];
lean_object* v_as_2325_ = _args[4];
lean_object* v_as_x27_2326_ = _args[5];
lean_object* v_b_2327_ = _args[6];
lean_object* v_a_2328_ = _args[7];
lean_object* v___y_2329_ = _args[8];
lean_object* v___y_2330_ = _args[9];
lean_object* v___y_2331_ = _args[10];
lean_object* v___y_2332_ = _args[11];
lean_object* v___y_2333_ = _args[12];
lean_object* v___y_2334_ = _args[13];
lean_object* v___y_2335_ = _args[14];
lean_object* v___y_2336_ = _args[15];
lean_object* v___y_2337_ = _args[16];
lean_object* v___y_2338_ = _args[17];
lean_object* v___y_2339_ = _args[18];
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__3(v_ctx_2321_, v_val_2322_, v___x_2323_, v___x_2324_, v_as_2325_, v_as_x27_2326_, v_b_2327_, v_a_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec(v_as_2325_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_00_u03b2_2341_, lean_object* v_m_2342_, lean_object* v_a_2343_, lean_object* v_b_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_m_2342_, v_a_2343_, v_b_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* v_n_2346_, lean_object* v_as_2347_, lean_object* v_lo_2348_, lean_object* v_hi_2349_, lean_object* v_w_2350_, lean_object* v_hlo_2351_, lean_object* v_hhi_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___redArg(v_as_2347_, v_lo_2348_, v_hi_2349_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* v_n_2354_, lean_object* v_as_2355_, lean_object* v_lo_2356_, lean_object* v_hi_2357_, lean_object* v_w_2358_, lean_object* v_hlo_2359_, lean_object* v_hhi_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__9(v_n_2354_, v_as_2355_, v_lo_2356_, v_hi_2357_, v_w_2358_, v_hlo_2359_, v_hhi_2360_);
lean_dec(v_hi_2357_);
lean_dec(v_n_2354_);
return v_res_2361_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2362_, lean_object* v_a_2363_, lean_object* v_x_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_2363_, v_x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2366_, lean_object* v_a_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2366_, v_a_2367_, v_x_2368_);
lean_dec(v_x_2368_);
lean_dec_ref(v_a_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(lean_object* v_00_u03b2_2371_, lean_object* v_data_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(lean_object* v_00_u03b2_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2375_, v_x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2378_, lean_object* v_a_2379_, lean_object* v_x_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_2378_, v_a_2379_, v_x_2380_);
lean_dec(v_x_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2381_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8(lean_object* v_00_u03b2_2382_, lean_object* v_a_2383_, lean_object* v_x_2384_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___redArg(v_a_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2386_, lean_object* v_a_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__8(v_00_u03b2_2386_, v_a_2387_, v_x_2388_);
lean_dec(v_x_2388_);
lean_dec_ref(v_a_2387_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9(lean_object* v_00_u03b2_2391_, lean_object* v_data_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9___redArg(v_data_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10(lean_object* v_00_u03b2_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v_x_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__10___redArg(v_a_2395_, v_b_2396_, v_x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2399_, lean_object* v_i_2400_, lean_object* v_source_2401_, lean_object* v_target_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_2400_, v_source_2401_, v_target_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11(lean_object* v_00_u03b2_2404_, lean_object* v_i_2405_, lean_object* v_source_2406_, lean_object* v_target_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11___redArg(v_i_2405_, v_source_2406_, v_target_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__15___redArg(v_x_2410_, v_x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20(lean_object* v_00_u03b2_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__4_spec__9_spec__11_spec__20___redArg(v_x_2414_, v_x_2415_);
return v___x_2416_;
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
