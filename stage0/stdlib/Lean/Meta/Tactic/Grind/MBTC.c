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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_SplitInfo_hash(lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isKnownCaseSplit___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 200, 238, 83, 121, 101, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 58, 101, 243, 41, 236, 253, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__3;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "skipping `mbtc`, maximum number of splits has been reached `(splits := "};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__5;
static const lean_string_object l_Lean_Meta_Grind_mbtc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_mbtc___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mbtc___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_mbtc___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mbtc___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4(lean_object* v_val_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
else
{
lean_object* v_head_326_; lean_object* v_tail_327_; lean_object* v_arg_328_; size_t v___x_329_; size_t v___x_330_; uint8_t v___x_331_; 
v_head_326_ = lean_ctor_get(v_x_324_, 0);
v_tail_327_ = lean_ctor_get(v_x_324_, 1);
v_arg_328_ = lean_ctor_get(v_head_326_, 0);
v___x_329_ = lean_ptr_addr(v_val_323_);
v___x_330_ = lean_ptr_addr(v_arg_328_);
v___x_331_ = lean_usize_dec_eq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
v_x_324_ = v_tail_327_;
goto _start;
}
else
{
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(lean_object* v_val_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4(v_val_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec_ref(v_val_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_mctx_346_; lean_object* v_lctx_347_; lean_object* v_options_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_343_ = lean_st_ref_get(v___y_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_339_);
v_mctx_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_mctx_346_);
lean_dec(v___x_345_);
v_lctx_347_ = lean_ctor_get(v___y_338_, 2);
v_options_348_ = lean_ctor_get(v___y_340_, 2);
lean_inc_ref(v_options_348_);
lean_inc_ref(v_lctx_347_);
v___x_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_349_, 0, v_env_344_);
lean_ctor_set(v___x_349_, 1, v_mctx_346_);
lean_ctor_set(v___x_349_, 2, v_lctx_347_);
lean_ctor_set(v___x_349_, 3, v_options_348_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_msgData_337_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_359_; double v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_float_of_nat(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(lean_object* v_cls_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_ref_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_417_; 
v_ref_371_ = lean_ctor_get(v___y_368_, 5);
v___x_372_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_417_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_417_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_417_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v_traceState_378_; lean_object* v_env_379_; lean_object* v_nextMacroScope_380_; lean_object* v_ngen_381_; lean_object* v_auxDeclNGen_382_; lean_object* v_cache_383_; lean_object* v_messages_384_; lean_object* v_infoState_385_; lean_object* v_snapshotTasks_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_416_; 
v___x_377_ = lean_st_ref_take(v___y_369_);
v_traceState_378_ = lean_ctor_get(v___x_377_, 4);
v_env_379_ = lean_ctor_get(v___x_377_, 0);
v_nextMacroScope_380_ = lean_ctor_get(v___x_377_, 1);
v_ngen_381_ = lean_ctor_get(v___x_377_, 2);
v_auxDeclNGen_382_ = lean_ctor_get(v___x_377_, 3);
v_cache_383_ = lean_ctor_get(v___x_377_, 5);
v_messages_384_ = lean_ctor_get(v___x_377_, 6);
v_infoState_385_ = lean_ctor_get(v___x_377_, 7);
v_snapshotTasks_386_ = lean_ctor_get(v___x_377_, 8);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_416_ == 0)
{
v___x_388_ = v___x_377_;
v_isShared_389_ = v_isSharedCheck_416_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snapshotTasks_386_);
lean_inc(v_infoState_385_);
lean_inc(v_messages_384_);
lean_inc(v_cache_383_);
lean_inc(v_traceState_378_);
lean_inc(v_auxDeclNGen_382_);
lean_inc(v_ngen_381_);
lean_inc(v_nextMacroScope_380_);
lean_inc(v_env_379_);
lean_dec(v___x_377_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_416_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint64_t v_tid_390_; lean_object* v_traces_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_415_; 
v_tid_390_ = lean_ctor_get_uint64(v_traceState_378_, sizeof(void*)*1);
v_traces_391_ = lean_ctor_get(v_traceState_378_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_traceState_378_);
if (v_isSharedCheck_415_ == 0)
{
v___x_393_ = v_traceState_378_;
v_isShared_394_ = v_isSharedCheck_415_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_traces_391_);
lean_dec(v_traceState_378_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_415_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; double v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
v___x_397_ = 0;
v___x_398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1));
v___x_399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_399_, 0, v_cls_364_);
lean_ctor_set(v___x_399_, 1, v___x_395_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_ctor_set_float(v___x_399_, sizeof(void*)*3, v___x_396_);
lean_ctor_set_float(v___x_399_, sizeof(void*)*3 + 8, v___x_396_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*3 + 16, v___x_397_);
v___x_400_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2));
v___x_401_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v_a_373_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
lean_inc(v_ref_371_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ref_371_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_PersistentArray_push___redArg(v_traces_391_, v___x_402_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_403_);
v___x_405_ = v___x_393_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_403_);
lean_ctor_set_uint64(v_reuseFailAlloc_414_, sizeof(void*)*1, v_tid_390_);
v___x_405_ = v_reuseFailAlloc_414_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v___x_405_);
v___x_407_ = v___x_388_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_env_379_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_380_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_381_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_382_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_messages_384_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_infoState_385_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_snapshotTasks_386_);
v___x_407_ = v_reuseFailAlloc_413_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_408_ = lean_st_ref_put(v___y_369_, v___x_407_);
v___x_409_ = lean_box(0);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_409_);
v___x_411_ = v___x_375_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(lean_object* v_cls_418_, lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_418_, v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg(lean_object* v_m_426_, lean_object* v_query_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_zero_431_; uint8_t v_isZero_432_; 
v_zero_431_ = lean_unsigned_to_nat(0u);
v_isZero_432_ = lean_nat_dec_eq(v_x_429_, v_zero_431_);
if (v_isZero_432_ == 1)
{
lean_dec(v_x_430_);
lean_dec(v_x_429_);
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_box(2);
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_val_434_ = lean_ctor_get(v_x_428_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v_x_428_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v_x_428_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_val_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_keyArray_442_; lean_object* v_valueArray_443_; lean_object* v___x_444_; uint8_t v_isSome_445_; 
v_keyArray_442_ = lean_ctor_get(v_m_426_, 1);
v_valueArray_443_ = lean_ctor_get(v_m_426_, 2);
v___x_444_ = lean_array_fget_borrowed(v_keyArray_442_, v_x_430_);
v_isSome_445_ = lean_noption_is_some(v___x_444_);
if (v_isSome_445_ == 0)
{
lean_dec(v_x_429_);
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_x_430_);
return v___x_446_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_x_430_);
v_val_447_ = lean_ctor_get(v_x_428_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_428_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v_x_428_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_val_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_one_455_; lean_object* v_n_456_; lean_object* v___y_458_; 
v_one_455_ = lean_unsigned_to_nat(1u);
v_n_456_ = lean_nat_sub(v_x_429_, v_one_455_);
lean_dec(v_x_429_);
if (v_isSome_445_ == 0)
{
goto v___jp_464_;
}
else
{
lean_object* v___x_466_; uint8_t v_isSome_467_; 
v___x_466_ = lean_array_fget_borrowed(v_valueArray_443_, v_x_430_);
v_isSome_467_ = lean_noption_is_some(v___x_466_);
if (v_isSome_467_ == 0)
{
goto v___jp_464_;
}
else
{
lean_object* v_val_468_; uint8_t v___x_469_; 
lean_inc(v___x_444_);
v_val_468_ = lean_noption_get(v___x_444_);
v___x_469_ = lean_expr_eqv(v_val_468_, v_query_427_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
lean_dec(v_val_468_);
v___x_470_ = lean_array_get_size(v_keyArray_442_);
v___x_471_ = lean_nat_add(v_x_430_, v_one_455_);
lean_dec(v_x_430_);
v___x_472_ = lean_nat_dec_lt(v___x_471_, v___x_470_);
if (v___x_472_ == 0)
{
lean_dec(v___x_471_);
v_x_429_ = v_n_456_;
v_x_430_ = v_zero_431_;
goto _start;
}
else
{
v_x_429_ = v_n_456_;
v_x_430_ = v___x_471_;
goto _start;
}
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; 
lean_dec(v_n_456_);
lean_dec(v_x_428_);
lean_inc(v___x_466_);
v_val_475_ = lean_noption_get(v___x_466_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_x_430_);
lean_ctor_set(v___x_476_, 1, v_val_468_);
lean_ctor_set(v___x_476_, 2, v_val_475_);
return v___x_476_;
}
}
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_array_get_size(v_keyArray_442_);
v___x_460_ = lean_nat_add(v_x_430_, v_one_455_);
lean_dec(v_x_430_);
v___x_461_ = lean_nat_dec_lt(v___x_460_, v___x_459_);
if (v___x_461_ == 0)
{
lean_dec(v___x_460_);
v_x_428_ = v___y_458_;
v_x_429_ = v_n_456_;
v_x_430_ = v_zero_431_;
goto _start;
}
else
{
v_x_428_ = v___y_458_;
v_x_429_ = v_n_456_;
v_x_430_ = v___x_460_;
goto _start;
}
}
v___jp_464_:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_465_; 
lean_inc(v_x_430_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_x_430_);
v___y_458_ = v___x_465_;
goto v___jp_457_;
}
else
{
v___y_458_ = v_x_428_;
goto v___jp_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg___boxed(lean_object* v_m_477_, lean_object* v_query_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg(v_m_477_, v_query_478_, v_x_479_, v_x_480_, v_x_481_);
lean_dec_ref(v_query_478_);
lean_dec_ref(v_m_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(lean_object* v_m_483_, lean_object* v_query_484_){
_start:
{
lean_object* v_keyArray_485_; lean_object* v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v_fold_490_; uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_keyArray_485_ = lean_ctor_get(v_m_483_, 1);
v___x_486_ = lean_array_get_size(v_keyArray_485_);
v___x_487_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_query_484_);
v___x_488_ = 32ULL;
v___x_489_ = lean_uint64_shift_right(v___x_487_, v___x_488_);
v_fold_490_ = lean_uint64_xor(v___x_487_, v___x_489_);
v___x_491_ = 16ULL;
v___x_492_ = lean_uint64_shift_right(v_fold_490_, v___x_491_);
v___x_493_ = lean_uint64_xor(v_fold_490_, v___x_492_);
v___x_494_ = lean_uint64_to_usize(v___x_493_);
v___x_495_ = lean_usize_of_nat(v___x_486_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_sub(v___x_495_, v___x_496_);
v___x_498_ = lean_usize_land(v___x_494_, v___x_497_);
v___x_499_ = lean_usize_to_nat(v___x_498_);
v___x_500_ = lean_box(0);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg(v_m_483_, v_query_484_, v___x_500_, v___x_486_, v___x_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg___boxed(lean_object* v_m_502_, lean_object* v_query_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_m_502_, v_query_503_);
lean_dec_ref(v_query_503_);
lean_dec_ref(v_m_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(lean_object* v_m_505_, lean_object* v_query_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_zero_510_; uint8_t v_isZero_511_; 
v_zero_510_ = lean_unsigned_to_nat(0u);
v_isZero_511_ = lean_nat_dec_eq(v_x_508_, v_zero_510_);
if (v_isZero_511_ == 1)
{
lean_dec(v_x_509_);
lean_dec(v_x_508_);
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_box(2);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_val_513_ = lean_ctor_get(v_x_507_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v_x_507_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v_x_507_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_val_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_keyArray_521_; lean_object* v_valueArray_522_; lean_object* v___x_523_; uint8_t v_isSome_524_; 
v_keyArray_521_ = lean_ctor_get(v_m_505_, 1);
v_valueArray_522_ = lean_ctor_get(v_m_505_, 2);
v___x_523_ = lean_array_fget_borrowed(v_keyArray_521_, v_x_509_);
v_isSome_524_ = lean_noption_is_some(v___x_523_);
if (v_isSome_524_ == 0)
{
lean_dec(v_x_508_);
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_x_509_);
return v___x_525_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_x_509_);
v_val_526_ = lean_ctor_get(v_x_507_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v_x_507_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_x_507_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_val_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_one_534_; lean_object* v_n_535_; lean_object* v___y_537_; 
v_one_534_ = lean_unsigned_to_nat(1u);
v_n_535_ = lean_nat_sub(v_x_508_, v_one_534_);
lean_dec(v_x_508_);
if (v_isSome_524_ == 0)
{
goto v___jp_543_;
}
else
{
lean_object* v___x_545_; uint8_t v_isSome_546_; 
v___x_545_ = lean_array_fget_borrowed(v_valueArray_522_, v_x_509_);
v_isSome_546_ = lean_noption_is_some(v___x_545_);
if (v_isSome_546_ == 0)
{
goto v___jp_543_;
}
else
{
lean_object* v_val_547_; uint8_t v___x_548_; 
lean_inc(v___x_523_);
v_val_547_ = lean_noption_get(v___x_523_);
v___x_548_ = l_Lean_Meta_Grind_SplitInfo_beq(v_val_547_, v_query_506_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_dec(v_val_547_);
v___x_549_ = lean_array_get_size(v_keyArray_521_);
v___x_550_ = lean_nat_add(v_x_509_, v_one_534_);
lean_dec(v_x_509_);
v___x_551_ = lean_nat_dec_lt(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
lean_dec(v___x_550_);
v_x_508_ = v_n_535_;
v_x_509_ = v_zero_510_;
goto _start;
}
else
{
v_x_508_ = v_n_535_;
v_x_509_ = v___x_550_;
goto _start;
}
}
else
{
lean_object* v_val_554_; lean_object* v___x_555_; 
lean_dec(v_n_535_);
lean_dec(v_x_507_);
lean_inc(v___x_545_);
v_val_554_ = lean_noption_get(v___x_545_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v_x_509_);
lean_ctor_set(v___x_555_, 1, v_val_547_);
lean_ctor_set(v___x_555_, 2, v_val_554_);
return v___x_555_;
}
}
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_array_get_size(v_keyArray_521_);
v___x_539_ = lean_nat_add(v_x_509_, v_one_534_);
lean_dec(v_x_509_);
v___x_540_ = lean_nat_dec_lt(v___x_539_, v___x_538_);
if (v___x_540_ == 0)
{
lean_dec(v___x_539_);
v_x_507_ = v___y_537_;
v_x_508_ = v_n_535_;
v_x_509_ = v_zero_510_;
goto _start;
}
else
{
v_x_507_ = v___y_537_;
v_x_508_ = v_n_535_;
v_x_509_ = v___x_539_;
goto _start;
}
}
v___jp_543_:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_544_; 
lean_inc(v_x_509_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_x_509_);
v___y_537_ = v___x_544_;
goto v___jp_536_;
}
else
{
v___y_537_ = v_x_507_;
goto v___jp_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(lean_object* v_m_556_, lean_object* v_query_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_m_556_, v_query_557_, v_x_558_, v_x_559_, v_x_560_);
lean_dec_ref(v_query_557_);
lean_dec_ref(v_m_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(lean_object* v_m_562_, lean_object* v_query_563_){
_start:
{
lean_object* v_keyArray_564_; lean_object* v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v_fold_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_keyArray_564_ = lean_ctor_get(v_m_562_, 1);
v___x_565_ = lean_array_get_size(v_keyArray_564_);
v___x_566_ = l_Lean_Meta_Grind_SplitInfo_hash(v_query_563_);
v___x_567_ = 32ULL;
v___x_568_ = lean_uint64_shift_right(v___x_566_, v___x_567_);
v_fold_569_ = lean_uint64_xor(v___x_566_, v___x_568_);
v___x_570_ = 16ULL;
v___x_571_ = lean_uint64_shift_right(v_fold_569_, v___x_570_);
v___x_572_ = lean_uint64_xor(v_fold_569_, v___x_571_);
v___x_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = lean_usize_of_nat(v___x_565_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_sub(v___x_574_, v___x_575_);
v___x_577_ = lean_usize_land(v___x_573_, v___x_576_);
v___x_578_ = lean_usize_to_nat(v___x_577_);
v___x_579_ = lean_box(0);
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_m_562_, v_query_563_, v___x_579_, v___x_565_, v___x_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg___boxed(lean_object* v_m_581_, lean_object* v_query_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_581_, v_query_582_);
lean_dec_ref(v_query_582_);
lean_dec_ref(v_m_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(lean_object* v_b_584_, lean_object* v_acc_585_, lean_object* v_i_586_){
_start:
{
lean_object* v___y_588_; lean_object* v_keyArray_596_; lean_object* v_valueArray_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_keyArray_596_ = lean_ctor_get(v_b_584_, 1);
v_valueArray_597_ = lean_ctor_get(v_b_584_, 2);
v___x_598_ = lean_array_get_size(v_keyArray_596_);
v___x_599_ = lean_nat_dec_lt(v_i_586_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v_i_586_);
return v_acc_585_;
}
else
{
lean_object* v___x_600_; uint8_t v_isSome_601_; 
v___x_600_ = lean_array_fget_borrowed(v_keyArray_596_, v_i_586_);
v_isSome_601_ = lean_noption_is_some(v___x_600_);
if (v_isSome_601_ == 0)
{
goto v___jp_592_;
}
else
{
lean_object* v___x_602_; uint8_t v_isSome_603_; 
v___x_602_ = lean_array_fget_borrowed(v_valueArray_597_, v_i_586_);
v_isSome_603_ = lean_noption_is_some(v___x_602_);
if (v_isSome_603_ == 0)
{
goto v___jp_592_;
}
else
{
lean_object* v_val_604_; lean_object* v_val_605_; lean_object* v_i_607_; lean_object* v___x_612_; 
lean_inc(v___x_600_);
v_val_604_ = lean_noption_get(v___x_600_);
lean_inc(v___x_602_);
v_val_605_ = lean_noption_get(v___x_602_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_acc_585_, v_val_604_);
switch(lean_obj_tag(v___x_612_))
{
case 0:
{
lean_object* v_index_613_; lean_object* v_size_614_; lean_object* v___x_615_; 
v_index_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_index_613_);
lean_dec_ref_known(v___x_612_, 3);
v_size_614_ = lean_ctor_get(v_acc_585_, 0);
lean_inc(v_size_614_);
v___x_615_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_585_, v_size_614_, v_index_613_, v_val_604_, v_val_605_);
lean_dec(v_index_613_);
v___y_588_ = v___x_615_;
goto v___jp_587_;
}
case 1:
{
lean_object* v_index_616_; 
v_index_616_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_index_616_);
lean_dec_ref_known(v___x_612_, 1);
v_i_607_ = v_index_616_;
goto v___jp_606_;
}
default: 
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_585_, v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_index_619_; 
v_index_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_index_619_);
lean_dec_ref_known(v___x_618_, 1);
v_i_607_ = v_index_619_;
goto v___jp_606_;
}
else
{
lean_dec(v_val_605_);
lean_dec(v_val_604_);
v___y_588_ = v_acc_585_;
goto v___jp_587_;
}
}
}
v___jp_606_:
{
lean_object* v_size_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_size_608_ = lean_ctor_get(v_acc_585_, 0);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_size_608_, v___x_609_);
v___x_611_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_585_, v___x_610_, v_i_607_, v_val_604_, v_val_605_);
lean_dec(v_i_607_);
v___y_588_ = v___x_611_;
goto v___jp_587_;
}
}
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_i_586_, v___x_589_);
lean_dec(v_i_586_);
v_acc_585_ = v___y_588_;
v_i_586_ = v___x_590_;
goto _start;
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_i_586_, v___x_593_);
lean_dec(v_i_586_);
v_i_586_ = v___x_594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_620_, lean_object* v_acc_621_, lean_object* v_i_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(v_b_620_, v_acc_621_, v_i_622_);
lean_dec_ref(v_b_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(lean_object* v_init_624_, lean_object* v_b_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(v_b_625_, v_init_624_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg___boxed(lean_object* v_init_628_, lean_object* v_b_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(v_init_628_, v_b_629_);
lean_dec_ref(v_b_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(lean_object* v_m_631_){
_start:
{
lean_object* v_keyArray_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_cellCount_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_target_639_; lean_object* v___x_640_; 
v_keyArray_632_ = lean_ctor_get(v_m_631_, 1);
v___x_633_ = lean_array_get_size(v_keyArray_632_);
v___x_634_ = lean_unsigned_to_nat(2u);
v_cellCount_635_ = lean_nat_mul(v___x_633_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_635_);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_635_);
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_635_);
v_target_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_639_, 0, v___x_636_);
lean_ctor_set(v_target_639_, 1, v___x_637_);
lean_ctor_set(v_target_639_, 2, v___x_638_);
v___x_640_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(v_target_639_, v_m_631_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(lean_object* v_m_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_641_);
lean_dec_ref(v_m_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(lean_object* v_ctx_643_, lean_object* v_val_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_as_x27_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
if (lean_obj_tag(v_as_x27_647_) == 0)
{
lean_object* v___x_660_; 
lean_dec(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v_val_644_);
lean_dec_ref(v_ctx_643_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_b_648_);
return v___x_660_;
}
else
{
lean_object* v_head_661_; lean_object* v_tail_662_; lean_object* v_eqAssignment_663_; lean_object* v_arg_664_; lean_object* v___x_665_; 
v_head_661_ = lean_ctor_get(v_as_x27_647_, 0);
v_tail_662_ = lean_ctor_get(v_as_x27_647_, 1);
v_eqAssignment_663_ = lean_ctor_get(v_ctx_643_, 2);
v_arg_664_ = lean_ctor_get(v_head_661_, 0);
lean_inc_ref(v_eqAssignment_663_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
lean_inc(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v_arg_664_);
lean_inc_ref(v_val_644_);
v___x_665_ = lean_apply_13(v_eqAssignment_663_, v_val_644_, v_arg_664_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, lean_box(0));
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; uint8_t v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
if (v___x_667_ == 0)
{
v_as_x27_647_ = v_tail_662_;
goto _start;
}
else
{
lean_object* v___x_669_; 
lean_inc_ref(v_arg_664_);
lean_inc_ref(v_val_644_);
v___x_669_ = l_Lean_Meta_Grind_hasSameType(v_val_644_, v_arg_664_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; uint8_t v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_unbox(v_a_670_);
lean_dec(v_a_670_);
if (v___x_671_ == 0)
{
v_as_x27_647_ = v_tail_662_;
goto _start;
}
else
{
lean_object* v___x_673_; 
lean_inc(v___x_646_);
lean_inc(v_head_661_);
lean_inc_ref(v___x_645_);
v___x_673_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_645_, v_head_661_, v___x_646_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___y_677_; lean_object* v_i_678_; lean_object* v___y_685_; lean_object* v___y_697_; lean_object* v_i_698_; lean_object* v___x_716_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_box(0);
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_648_, v_a_674_);
switch(lean_obj_tag(v___x_716_))
{
case 0:
{
lean_dec_ref_known(v___x_716_, 3);
lean_dec(v_a_674_);
v_as_x27_647_ = v_tail_662_;
goto _start;
}
case 1:
{
lean_object* v_index_718_; lean_object* v_size_719_; lean_object* v_keyArray_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_index_718_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_index_718_);
lean_dec_ref_known(v___x_716_, 1);
v_size_719_ = lean_ctor_get(v_b_648_, 0);
v_keyArray_720_ = lean_ctor_get(v_b_648_, 1);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_size_719_, v___x_721_);
v___x_723_ = lean_array_get_size(v_keyArray_720_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v___x_722_);
lean_dec(v_index_718_);
goto v___jp_704_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_725_ = lean_unsigned_to_nat(4u);
v___x_726_ = lean_nat_mul(v___x_722_, v___x_725_);
v___x_727_ = lean_unsigned_to_nat(3u);
v___x_728_ = lean_nat_mul(v___x_723_, v___x_727_);
v___x_729_ = lean_nat_dec_le(v___x_726_, v___x_728_);
lean_dec(v___x_728_);
lean_dec(v___x_726_);
if (v___x_729_ == 0)
{
lean_dec(v___x_722_);
lean_dec(v_index_718_);
goto v___jp_704_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_648_, v___x_722_, v_index_718_, v_a_674_, v___x_675_);
lean_dec(v_index_718_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_730_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_732_; lean_object* v_keyArray_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_size_732_ = lean_ctor_get(v_b_648_, 0);
v_keyArray_733_ = lean_ctor_get(v_b_648_, 1);
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_size_732_, v___x_734_);
v___x_736_ = lean_array_get_size(v_keyArray_733_);
v___x_737_ = lean_nat_dec_lt(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v___x_735_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_b_648_);
lean_dec_ref(v_b_648_);
v___y_685_ = v___x_738_;
goto v___jp_684_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_mul(v___x_735_, v___x_739_);
lean_dec(v___x_735_);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_nat_mul(v___x_736_, v___x_741_);
v___x_743_ = lean_nat_dec_le(v___x_740_, v___x_742_);
lean_dec(v___x_742_);
lean_dec(v___x_740_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_b_648_);
lean_dec_ref(v_b_648_);
v___y_685_ = v___x_744_;
goto v___jp_684_;
}
else
{
v___y_685_ = v_b_648_;
goto v___jp_684_;
}
}
}
}
v___jp_676_:
{
lean_object* v_size_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_size_679_ = lean_ctor_get(v___y_677_, 0);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_size_679_, v___x_680_);
v___x_682_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_677_, v___x_681_, v_i_678_, v_a_674_, v___x_675_);
lean_dec(v_i_678_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_682_;
goto _start;
}
v___jp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v___y_685_, v_a_674_);
switch(lean_obj_tag(v___x_686_))
{
case 0:
{
lean_object* v_index_687_; lean_object* v_size_688_; lean_object* v___x_689_; 
v_index_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_index_687_);
lean_dec_ref_known(v___x_686_, 3);
v_size_688_ = lean_ctor_get(v___y_685_, 0);
lean_inc(v_size_688_);
v___x_689_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_685_, v_size_688_, v_index_687_, v_a_674_, v___x_675_);
lean_dec(v_index_687_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_689_;
goto _start;
}
case 1:
{
lean_object* v_index_691_; 
v_index_691_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_index_691_);
lean_dec_ref_known(v___x_686_, 1);
v___y_677_ = v___y_685_;
v_i_678_ = v_index_691_;
goto v___jp_676_;
}
default: 
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_685_, v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_index_694_; 
v_index_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_index_694_);
lean_dec_ref_known(v___x_693_, 1);
v___y_677_ = v___y_685_;
v_i_678_ = v_index_694_;
goto v___jp_676_;
}
else
{
lean_dec(v_a_674_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___y_685_;
goto _start;
}
}
}
}
v___jp_696_:
{
lean_object* v_size_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_size_699_ = lean_ctor_get(v___y_697_, 0);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_add(v_size_699_, v___x_700_);
v___x_702_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_697_, v___x_701_, v_i_698_, v_a_674_, v___x_675_);
lean_dec(v_i_698_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_702_;
goto _start;
}
v___jp_704_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_b_648_);
lean_dec_ref(v_b_648_);
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v___x_705_, v_a_674_);
switch(lean_obj_tag(v___x_706_))
{
case 0:
{
lean_object* v_index_707_; lean_object* v_size_708_; lean_object* v___x_709_; 
v_index_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_index_707_);
lean_dec_ref_known(v___x_706_, 3);
v_size_708_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_size_708_);
v___x_709_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_705_, v_size_708_, v_index_707_, v_a_674_, v___x_675_);
lean_dec(v_index_707_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_709_;
goto _start;
}
case 1:
{
lean_object* v_index_711_; 
v_index_711_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_index_711_);
lean_dec_ref_known(v___x_706_, 1);
v___y_697_ = v___x_705_;
v_i_698_ = v_index_711_;
goto v___jp_696_;
}
default: 
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_705_, v___x_712_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_index_714_; 
v_index_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_index_714_);
lean_dec_ref_known(v___x_713_, 1);
v___y_697_ = v___x_705_;
v_i_698_ = v_index_714_;
goto v___jp_696_;
}
else
{
lean_dec(v_a_674_);
v_as_x27_647_ = v_tail_662_;
v_b_648_ = v___x_705_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_b_648_);
lean_dec(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v_val_644_);
lean_dec_ref(v_ctx_643_);
v_a_745_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_673_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_673_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_b_648_);
lean_dec(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v_val_644_);
lean_dec_ref(v_ctx_643_);
v_a_753_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_669_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_669_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v_b_648_);
lean_dec(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v_val_644_);
lean_dec_ref(v_ctx_643_);
v_a_761_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_665_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_665_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_ctx_769_ = _args[0];
lean_object* v_val_770_ = _args[1];
lean_object* v___x_771_ = _args[2];
lean_object* v___x_772_ = _args[3];
lean_object* v_as_x27_773_ = _args[4];
lean_object* v_b_774_ = _args[5];
lean_object* v___y_775_ = _args[6];
lean_object* v___y_776_ = _args[7];
lean_object* v___y_777_ = _args[8];
lean_object* v___y_778_ = _args[9];
lean_object* v___y_779_ = _args[10];
lean_object* v___y_780_ = _args[11];
lean_object* v___y_781_ = _args[12];
lean_object* v___y_782_ = _args[13];
lean_object* v___y_783_ = _args[14];
lean_object* v___y_784_ = _args[15];
lean_object* v___y_785_ = _args[16];
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_ctx_769_, v_val_770_, v___x_771_, v___x_772_, v_as_x27_773_, v_b_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v_as_x27_773_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg(lean_object* v_b_787_, lean_object* v_acc_788_, lean_object* v_i_789_){
_start:
{
lean_object* v___y_791_; lean_object* v_keyArray_799_; lean_object* v_valueArray_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_keyArray_799_ = lean_ctor_get(v_b_787_, 1);
v_valueArray_800_ = lean_ctor_get(v_b_787_, 2);
v___x_801_ = lean_array_get_size(v_keyArray_799_);
v___x_802_ = lean_nat_dec_lt(v_i_789_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v_i_789_);
return v_acc_788_;
}
else
{
lean_object* v___x_803_; uint8_t v_isSome_804_; 
v___x_803_ = lean_array_fget_borrowed(v_keyArray_799_, v_i_789_);
v_isSome_804_ = lean_noption_is_some(v___x_803_);
if (v_isSome_804_ == 0)
{
goto v___jp_795_;
}
else
{
lean_object* v___x_805_; uint8_t v_isSome_806_; 
v___x_805_ = lean_array_fget_borrowed(v_valueArray_800_, v_i_789_);
v_isSome_806_ = lean_noption_is_some(v___x_805_);
if (v_isSome_806_ == 0)
{
goto v___jp_795_;
}
else
{
lean_object* v_val_807_; lean_object* v_val_808_; lean_object* v_i_810_; lean_object* v___x_815_; 
lean_inc(v___x_803_);
v_val_807_ = lean_noption_get(v___x_803_);
lean_inc(v___x_805_);
v_val_808_ = lean_noption_get(v___x_805_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_acc_788_, v_val_807_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_index_816_; lean_object* v_size_817_; lean_object* v___x_818_; 
v_index_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_index_816_);
lean_dec_ref_known(v___x_815_, 3);
v_size_817_ = lean_ctor_get(v_acc_788_, 0);
lean_inc(v_size_817_);
v___x_818_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_788_, v_size_817_, v_index_816_, v_val_807_, v_val_808_);
lean_dec(v_index_816_);
v___y_791_ = v___x_818_;
goto v___jp_790_;
}
case 1:
{
lean_object* v_index_819_; 
v_index_819_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_index_819_);
lean_dec_ref_known(v___x_815_, 1);
v_i_810_ = v_index_819_;
goto v___jp_809_;
}
default: 
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_788_, v___x_820_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_index_822_; 
v_index_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_index_822_);
lean_dec_ref_known(v___x_821_, 1);
v_i_810_ = v_index_822_;
goto v___jp_809_;
}
else
{
lean_dec(v_val_808_);
lean_dec(v_val_807_);
v___y_791_ = v_acc_788_;
goto v___jp_790_;
}
}
}
v___jp_809_:
{
lean_object* v_size_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_size_811_ = lean_ctor_get(v_acc_788_, 0);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v_size_811_, v___x_812_);
v___x_814_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_788_, v___x_813_, v_i_810_, v_val_807_, v_val_808_);
lean_dec(v_i_810_);
v___y_791_ = v___x_814_;
goto v___jp_790_;
}
}
}
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_i_789_, v___x_792_);
lean_dec(v_i_789_);
v_acc_788_ = v___y_791_;
v_i_789_ = v___x_793_;
goto _start;
}
v___jp_795_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_i_789_, v___x_796_);
lean_dec(v_i_789_);
v_i_789_ = v___x_797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg___boxed(lean_object* v_b_823_, lean_object* v_acc_824_, lean_object* v_i_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg(v_b_823_, v_acc_824_, v_i_825_);
lean_dec_ref(v_b_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg(lean_object* v_init_827_, lean_object* v_b_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg(v_b_828_, v_init_827_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg___boxed(lean_object* v_init_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg(v_init_831_, v_b_832_);
lean_dec_ref(v_b_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(lean_object* v_m_834_){
_start:
{
lean_object* v_keyArray_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_cellCount_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_target_842_; lean_object* v___x_843_; 
v_keyArray_835_ = lean_ctor_get(v_m_834_, 1);
v___x_836_ = lean_array_get_size(v_keyArray_835_);
v___x_837_ = lean_unsigned_to_nat(2u);
v_cellCount_838_ = lean_nat_mul(v___x_836_, v___x_837_);
v___x_839_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_838_);
v___x_840_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_838_);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_838_);
v_target_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_842_, 0, v___x_839_);
lean_ctor_set(v_target_842_, 1, v___x_840_);
lean_ctor_set(v_target_842_, 2, v___x_841_);
v___x_843_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg(v_target_842_, v_m_834_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg___boxed(lean_object* v_m_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_m_844_);
lean_dec_ref(v_m_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(lean_object* v_m_846_, lean_object* v_query_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_m_846_, v_query_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_index_849_; lean_object* v_key_850_; lean_object* v_value_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_index_849_ = lean_ctor_get(v___x_848_, 0);
v_key_850_ = lean_ctor_get(v___x_848_, 1);
v_value_851_ = lean_ctor_get(v___x_848_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_848_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_value_851_);
lean_inc(v_key_850_);
lean_inc(v_index_849_);
lean_dec(v___x_848_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_index_849_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_key_850_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_value_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v___x_848_);
v___x_859_ = lean_box(1);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg___boxed(lean_object* v_m_860_, lean_object* v_query_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(v_m_860_, v_query_861_);
lean_dec_ref(v_query_861_);
lean_dec_ref(v_m_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(v_m_863_, v_a_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_value_866_; lean_object* v___x_867_; 
v_value_866_ = lean_ctor_get(v___x_865_, 2);
lean_inc(v_value_866_);
lean_dec_ref_known(v___x_865_, 3);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v_value_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_box(0);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg___boxed(lean_object* v_m_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_m_869_, v_a_870_);
lean_dec_ref(v_a_870_);
lean_dec_ref(v_m_869_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3));
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__5));
v___x_884_ = l_Lean_Name_append(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__7));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__9));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(lean_object* v_e_891_, lean_object* v_ctx_892_, lean_object* v___x_893_, lean_object* v_as_894_, size_t v_sz_895_, size_t v_i_896_, lean_object* v_b_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_a_910_; uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_lt(v_i_896_, v_sz_895_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec_ref(v___x_893_);
lean_dec_ref(v_ctx_892_);
lean_dec_ref(v_e_891_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_897_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v_snd_917_; lean_object* v_fst_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_1174_; 
v___x_916_ = lean_st_ref_get(v___y_898_);
v_snd_917_ = lean_ctor_get(v_b_897_, 1);
v_fst_918_ = lean_ctor_get(v_b_897_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_b_897_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_920_ = v_b_897_;
v_isShared_921_ = v_isSharedCheck_1174_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_snd_917_);
lean_inc(v_fst_918_);
lean_dec(v_b_897_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_1174_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_fst_922_; lean_object* v_snd_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1173_; 
v_fst_922_ = lean_ctor_get(v_snd_917_, 0);
v_snd_923_ = lean_ctor_get(v_snd_917_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_snd_917_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_925_ = v_snd_917_;
v_isShared_926_ = v_isSharedCheck_1173_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snd_923_);
lean_inc(v_fst_922_);
lean_dec(v_snd_917_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1173_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_map_928_; lean_object* v_candidates_929_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v_i_943_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_i_966_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v_i_988_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v_i_1009_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_array_uget_borrowed(v_as_894_, v_i_896_);
v___x_1027_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_916_, v_a_1026_);
lean_dec(v___x_916_);
if (lean_obj_tag(v___x_1027_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1170_; 
v_val_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1170_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1170_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_hasTheoryVar_1130_; lean_object* v___x_1131_; 
v_hasTheoryVar_1130_ = lean_ctor_get(v_ctx_892_, 1);
lean_inc_ref(v_hasTheoryVar_1130_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v___y_899_);
lean_inc(v___y_898_);
lean_inc(v_val_1028_);
v___x_1131_ = lean_apply_12(v_hasTheoryVar_1130_, v_val_1028_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; uint8_t v___x_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = lean_unbox(v_a_1132_);
lean_dec(v_a_1132_);
if (v___x_1133_ == 0)
{
lean_del_object(v___x_1030_);
lean_dec(v_val_1028_);
v_map_928_ = v_fst_918_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
else
{
lean_object* v_options_1134_; uint8_t v_hasTrace_1135_; 
v_options_1134_ = lean_ctor_get(v___y_906_, 2);
v_hasTrace_1135_ = lean_ctor_get_uint8(v_options_1134_, sizeof(void*)*1);
if (v_hasTrace_1135_ == 0)
{
lean_del_object(v___x_1030_);
v___y_1033_ = v___y_898_;
v___y_1034_ = v___y_899_;
v___y_1035_ = v___y_900_;
v___y_1036_ = v___y_901_;
v___y_1037_ = v___y_902_;
v___y_1038_ = v___y_903_;
v___y_1039_ = v___y_904_;
v___y_1040_ = v___y_905_;
v___y_1041_ = v___y_906_;
v___y_1042_ = v___y_907_;
goto v___jp_1032_;
}
else
{
lean_object* v_inheritedTraceOptions_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_inheritedTraceOptions_1136_ = lean_ctor_get(v___y_906_, 13);
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__3));
v___x_1138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__6);
v___x_1139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1136_, v_options_1134_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_del_object(v___x_1030_);
v___y_1033_ = v___y_898_;
v___y_1034_ = v___y_899_;
v___y_1035_ = v___y_900_;
v___y_1036_ = v___y_901_;
v___y_1037_ = v___y_902_;
v___y_1038_ = v___y_903_;
v___y_1039_ = v___y_904_;
v___y_1040_ = v___y_905_;
v___y_1041_ = v___y_906_;
v___y_1042_ = v___y_907_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_inc(v_val_1028_);
v___x_1140_ = l_Lean_MessageData_ofExpr(v_val_1028_);
v___x_1141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__8);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
lean_inc_ref(v___x_893_);
v___x_1143_ = l_Lean_MessageData_ofExpr(v___x_893_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__10);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
lean_inc(v_snd_923_);
v___x_1147_ = l_Nat_reprFast(v_snd_923_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 3);
lean_ctor_set(v___x_1030_, 0, v___x_1147_);
v___x_1149_ = v___x_1030_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_MessageData_ofFormat(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1146_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_1137_, v___x_1151_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_dec_ref_known(v___x_1152_, 1);
v___y_1033_ = v___y_898_;
v___y_1034_ = v___y_899_;
v___y_1035_ = v___y_900_;
v___y_1036_ = v___y_901_;
v___y_1037_ = v___y_902_;
v___y_1038_ = v___y_903_;
v___y_1039_ = v___y_904_;
v___y_1040_ = v___y_905_;
v___y_1041_ = v___y_906_;
v___y_1042_ = v___y_907_;
goto v___jp_1032_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_val_1028_);
lean_del_object(v___x_925_);
lean_dec(v_snd_923_);
lean_dec(v_fst_922_);
lean_del_object(v___x_920_);
lean_dec(v_fst_918_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v_ctx_892_);
lean_dec_ref(v_e_891_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
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
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_del_object(v___x_1030_);
lean_dec(v_val_1028_);
lean_del_object(v___x_925_);
lean_dec(v_snd_923_);
lean_dec(v_fst_922_);
lean_del_object(v___x_920_);
lean_dec(v_fst_918_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v_ctx_892_);
lean_dec_ref(v_e_891_);
v_a_1162_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1131_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1131_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
v___jp_1032_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_inc_ref_n(v_e_891_, 2);
lean_inc(v_val_1028_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_val_1028_);
lean_ctor_set(v___x_1043_, 1, v_e_891_);
v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(v_e_891_, v_snd_923_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_fst_918_, v_a_1045_);
if (lean_obj_tag(v___x_1046_) == 1)
{
lean_object* v_val_1047_; uint8_t v___x_1048_; 
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__4(v_val_1028_, v_val_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_inc(v_snd_923_);
lean_inc_ref(v___x_1043_);
lean_inc_ref(v_ctx_892_);
v___x_1049_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_ctx_892_, v_val_1028_, v___x_1043_, v_snd_923_, v_val_1047_, v_fst_922_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1043_);
lean_ctor_set(v___x_1051_, 1, v_val_1047_);
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_fst_918_, v_a_1045_);
switch(lean_obj_tag(v___x_1052_))
{
case 0:
{
lean_object* v_index_1053_; lean_object* v_size_1054_; lean_object* v___x_1055_; 
v_index_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_index_1053_);
lean_dec_ref_known(v___x_1052_, 3);
v_size_1054_ = lean_ctor_get(v_fst_918_, 0);
lean_inc(v_size_1054_);
v___x_1055_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_918_, v_size_1054_, v_index_1053_, v_a_1045_, v___x_1051_);
lean_dec(v_index_1053_);
v_map_928_ = v___x_1055_;
v_candidates_929_ = v_a_1050_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_1056_; lean_object* v_size_1057_; lean_object* v_keyArray_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_index_1056_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_index_1056_);
lean_dec_ref_known(v___x_1052_, 1);
v_size_1057_ = lean_ctor_get(v_fst_918_, 0);
v_keyArray_1058_ = lean_ctor_get(v_fst_918_, 1);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_size_1057_, v___x_1059_);
v___x_1061_ = lean_array_get_size(v_keyArray_1058_);
v___x_1062_ = lean_nat_dec_lt(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec(v___x_1060_);
lean_dec(v_index_1056_);
v___y_972_ = v___x_1051_;
v___y_973_ = v_a_1045_;
v___y_974_ = v_a_1050_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1063_ = lean_unsigned_to_nat(4u);
v___x_1064_ = lean_nat_mul(v___x_1060_, v___x_1063_);
v___x_1065_ = lean_unsigned_to_nat(3u);
v___x_1066_ = lean_nat_mul(v___x_1061_, v___x_1065_);
v___x_1067_ = lean_nat_dec_le(v___x_1064_, v___x_1066_);
lean_dec(v___x_1066_);
lean_dec(v___x_1064_);
if (v___x_1067_ == 0)
{
lean_dec(v___x_1060_);
lean_dec(v_index_1056_);
v___y_972_ = v___x_1051_;
v___y_973_ = v_a_1045_;
v___y_974_ = v_a_1050_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_918_, v___x_1060_, v_index_1056_, v_a_1045_, v___x_1051_);
lean_dec(v_index_1056_);
v_map_928_ = v___x_1068_;
v_candidates_929_ = v_a_1050_;
goto v___jp_927_;
}
}
}
default: 
{
lean_object* v_size_1069_; lean_object* v_keyArray_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_size_1069_ = lean_ctor_get(v_fst_918_, 0);
v_keyArray_1070_ = lean_ctor_get(v_fst_918_, 1);
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_add(v_size_1069_, v___x_1071_);
v___x_1073_ = lean_array_get_size(v_keyArray_1070_);
v___x_1074_ = lean_nat_dec_lt(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v___x_1072_);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___y_949_ = v___x_1051_;
v___y_950_ = v_a_1045_;
v___y_951_ = v_a_1050_;
v___y_952_ = v___x_1075_;
goto v___jp_948_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1076_ = lean_unsigned_to_nat(4u);
v___x_1077_ = lean_nat_mul(v___x_1072_, v___x_1076_);
lean_dec(v___x_1072_);
v___x_1078_ = lean_unsigned_to_nat(3u);
v___x_1079_ = lean_nat_mul(v___x_1073_, v___x_1078_);
v___x_1080_ = lean_nat_dec_le(v___x_1077_, v___x_1079_);
lean_dec(v___x_1079_);
lean_dec(v___x_1077_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___y_949_ = v___x_1051_;
v___y_950_ = v_a_1045_;
v___y_951_ = v_a_1050_;
v___y_952_ = v___x_1081_;
goto v___jp_948_;
}
else
{
v___y_949_ = v___x_1051_;
v___y_950_ = v_a_1045_;
v___y_951_ = v_a_1050_;
v___y_952_ = v_fst_918_;
goto v___jp_948_;
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_val_1047_);
lean_dec(v_a_1045_);
lean_dec_ref_known(v___x_1043_, 2);
lean_del_object(v___x_925_);
lean_dec(v_snd_923_);
lean_del_object(v___x_920_);
lean_dec(v_fst_918_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v_ctx_892_);
lean_dec_ref(v_e_891_);
v_a_1082_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1049_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1049_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_dec(v_val_1047_);
lean_dec(v_a_1045_);
lean_dec_ref_known(v___x_1043_, 2);
lean_dec(v_val_1028_);
v_map_928_ = v_fst_918_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v___x_1046_);
lean_dec(v_val_1028_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1043_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_fst_918_, v_a_1045_);
switch(lean_obj_tag(v___x_1092_))
{
case 0:
{
lean_object* v_index_1093_; lean_object* v_size_1094_; lean_object* v___x_1095_; 
v_index_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_index_1093_);
lean_dec_ref_known(v___x_1092_, 3);
v_size_1094_ = lean_ctor_get(v_fst_918_, 0);
lean_inc(v_size_1094_);
v___x_1095_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_918_, v_size_1094_, v_index_1093_, v_a_1045_, v___x_1091_);
lean_dec(v_index_1093_);
v_map_928_ = v___x_1095_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_1096_; lean_object* v_size_1097_; lean_object* v_keyArray_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_index_1096_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_index_1096_);
lean_dec_ref_known(v___x_1092_, 1);
v_size_1097_ = lean_ctor_get(v_fst_918_, 0);
v_keyArray_1098_ = lean_ctor_get(v_fst_918_, 1);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v_size_1097_, v___x_1099_);
v___x_1101_ = lean_array_get_size(v_keyArray_1098_);
v___x_1102_ = lean_nat_dec_lt(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec(v___x_1100_);
lean_dec(v_index_1096_);
v___y_1015_ = v_a_1045_;
v___y_1016_ = v___x_1091_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1103_ = lean_unsigned_to_nat(4u);
v___x_1104_ = lean_nat_mul(v___x_1100_, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(3u);
v___x_1106_ = lean_nat_mul(v___x_1101_, v___x_1105_);
v___x_1107_ = lean_nat_dec_le(v___x_1104_, v___x_1106_);
lean_dec(v___x_1106_);
lean_dec(v___x_1104_);
if (v___x_1107_ == 0)
{
lean_dec(v___x_1100_);
lean_dec(v_index_1096_);
v___y_1015_ = v_a_1045_;
v___y_1016_ = v___x_1091_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_918_, v___x_1100_, v_index_1096_, v_a_1045_, v___x_1091_);
lean_dec(v_index_1096_);
v_map_928_ = v___x_1108_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
}
}
default: 
{
lean_object* v_size_1109_; lean_object* v_keyArray_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_size_1109_ = lean_ctor_get(v_fst_918_, 0);
v_keyArray_1110_ = lean_ctor_get(v_fst_918_, 1);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_size_1109_, v___x_1111_);
v___x_1113_ = lean_array_get_size(v_keyArray_1110_);
v___x_1114_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v___x_1112_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___y_994_ = v_a_1045_;
v___y_995_ = v___x_1091_;
v___y_996_ = v___x_1115_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1116_ = lean_unsigned_to_nat(4u);
v___x_1117_ = lean_nat_mul(v___x_1112_, v___x_1116_);
lean_dec(v___x_1112_);
v___x_1118_ = lean_unsigned_to_nat(3u);
v___x_1119_ = lean_nat_mul(v___x_1113_, v___x_1118_);
v___x_1120_ = lean_nat_dec_le(v___x_1117_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec(v___x_1117_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___y_994_ = v_a_1045_;
v___y_995_ = v___x_1091_;
v___y_996_ = v___x_1121_;
goto v___jp_993_;
}
else
{
v___y_994_ = v_a_1045_;
v___y_995_ = v___x_1091_;
v___y_996_ = v_fst_918_;
goto v___jp_993_;
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref_known(v___x_1043_, 2);
lean_dec(v_val_1028_);
lean_del_object(v___x_925_);
lean_dec(v_snd_923_);
lean_dec(v_fst_922_);
lean_del_object(v___x_920_);
lean_dec(v_fst_918_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v_ctx_892_);
lean_dec_ref(v_e_891_);
v_a_1122_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1044_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1044_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v___x_1027_);
lean_del_object(v___x_925_);
lean_del_object(v___x_920_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_fst_922_);
lean_ctor_set(v___x_1171_, 1, v_snd_923_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_fst_918_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v_a_910_ = v___x_1172_;
goto v___jp_909_;
}
v___jp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_add(v_snd_923_, v___x_930_);
lean_dec(v_snd_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_931_);
lean_ctor_set(v___x_925_, 0, v_candidates_929_);
v___x_933_ = v___x_925_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_candidates_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_933_);
lean_ctor_set(v___x_920_, 0, v_map_928_);
v___x_935_ = v___x_920_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_map_928_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
v_a_910_ = v___x_935_;
goto v___jp_909_;
}
}
}
v___jp_938_:
{
lean_object* v_size_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_size_944_ = lean_ctor_get(v___y_940_, 0);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_size_944_, v___x_945_);
v___x_947_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_940_, v___x_946_, v_i_943_, v___y_941_, v___y_939_);
lean_dec(v_i_943_);
v_map_928_ = v___x_947_;
v_candidates_929_ = v___y_942_;
goto v___jp_927_;
}
v___jp_948_:
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v___y_952_, v___y_950_);
switch(lean_obj_tag(v___x_953_))
{
case 0:
{
lean_object* v_index_954_; lean_object* v_size_955_; lean_object* v___x_956_; 
v_index_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_index_954_);
lean_dec_ref_known(v___x_953_, 3);
v_size_955_ = lean_ctor_get(v___y_952_, 0);
lean_inc(v_size_955_);
v___x_956_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_952_, v_size_955_, v_index_954_, v___y_950_, v___y_949_);
lean_dec(v_index_954_);
v_map_928_ = v___x_956_;
v_candidates_929_ = v___y_951_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_957_; 
v_index_957_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_index_957_);
lean_dec_ref_known(v___x_953_, 1);
v___y_939_ = v___y_949_;
v___y_940_ = v___y_952_;
v___y_941_ = v___y_950_;
v___y_942_ = v___y_951_;
v_i_943_ = v_index_957_;
goto v___jp_938_;
}
default: 
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_952_, v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_index_960_; 
v_index_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_index_960_);
lean_dec_ref_known(v___x_959_, 1);
v___y_939_ = v___y_949_;
v___y_940_ = v___y_952_;
v___y_941_ = v___y_950_;
v___y_942_ = v___y_951_;
v_i_943_ = v_index_960_;
goto v___jp_938_;
}
else
{
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
v_map_928_ = v___y_952_;
v_candidates_929_ = v___y_951_;
goto v___jp_927_;
}
}
}
}
v___jp_961_:
{
lean_object* v_size_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_size_967_ = lean_ctor_get(v___y_963_, 0);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_size_967_, v___x_968_);
v___x_970_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_963_, v___x_969_, v_i_966_, v___y_964_, v___y_962_);
lean_dec(v_i_966_);
v_map_928_ = v___x_970_;
v_candidates_929_ = v___y_965_;
goto v___jp_927_;
}
v___jp_971_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v___x_975_, v___y_973_);
switch(lean_obj_tag(v___x_976_))
{
case 0:
{
lean_object* v_index_977_; lean_object* v_size_978_; lean_object* v___x_979_; 
v_index_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_977_);
lean_dec_ref_known(v___x_976_, 3);
v_size_978_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_size_978_);
v___x_979_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_975_, v_size_978_, v_index_977_, v___y_973_, v___y_972_);
lean_dec(v_index_977_);
v_map_928_ = v___x_979_;
v_candidates_929_ = v___y_974_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_980_; 
v_index_980_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_980_);
lean_dec_ref_known(v___x_976_, 1);
v___y_962_ = v___y_972_;
v___y_963_ = v___x_975_;
v___y_964_ = v___y_973_;
v___y_965_ = v___y_974_;
v_i_966_ = v_index_980_;
goto v___jp_961_;
}
default: 
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_975_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_index_983_; 
v_index_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_index_983_);
lean_dec_ref_known(v___x_982_, 1);
v___y_962_ = v___y_972_;
v___y_963_ = v___x_975_;
v___y_964_ = v___y_973_;
v___y_965_ = v___y_974_;
v_i_966_ = v_index_983_;
goto v___jp_961_;
}
else
{
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
v_map_928_ = v___x_975_;
v_candidates_929_ = v___y_974_;
goto v___jp_927_;
}
}
}
}
v___jp_984_:
{
lean_object* v_size_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_size_989_ = lean_ctor_get(v___y_987_, 0);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_size_989_, v___x_990_);
v___x_992_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_987_, v___x_991_, v_i_988_, v___y_985_, v___y_986_);
lean_dec(v_i_988_);
v_map_928_ = v___x_992_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
v___jp_993_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v___y_996_, v___y_994_);
switch(lean_obj_tag(v___x_997_))
{
case 0:
{
lean_object* v_index_998_; lean_object* v_size_999_; lean_object* v___x_1000_; 
v_index_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_index_998_);
lean_dec_ref_known(v___x_997_, 3);
v_size_999_ = lean_ctor_get(v___y_996_, 0);
lean_inc(v_size_999_);
v___x_1000_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_996_, v_size_999_, v_index_998_, v___y_994_, v___y_995_);
lean_dec(v_index_998_);
v_map_928_ = v___x_1000_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_1001_; 
v_index_1001_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_index_1001_);
lean_dec_ref_known(v___x_997_, 1);
v___y_985_ = v___y_994_;
v___y_986_ = v___y_995_;
v___y_987_ = v___y_996_;
v_i_988_ = v_index_1001_;
goto v___jp_984_;
}
default: 
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_996_, v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_index_1004_; 
v_index_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_index_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___y_985_ = v___y_994_;
v___y_986_ = v___y_995_;
v___y_987_ = v___y_996_;
v_i_988_ = v_index_1004_;
goto v___jp_984_;
}
else
{
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
v_map_928_ = v___y_996_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
}
}
}
v___jp_1005_:
{
lean_object* v_size_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_size_1010_ = lean_ctor_get(v___y_1006_, 0);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_size_1010_, v___x_1011_);
v___x_1013_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1006_, v___x_1012_, v_i_1009_, v___y_1007_, v___y_1008_);
lean_dec(v_i_1009_);
v_map_928_ = v___x_1013_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
v___jp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_fst_918_);
lean_dec(v_fst_918_);
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v___x_1017_, v___y_1015_);
switch(lean_obj_tag(v___x_1018_))
{
case 0:
{
lean_object* v_index_1019_; lean_object* v_size_1020_; lean_object* v___x_1021_; 
v_index_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_index_1019_);
lean_dec_ref_known(v___x_1018_, 3);
v_size_1020_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_size_1020_);
v___x_1021_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1017_, v_size_1020_, v_index_1019_, v___y_1015_, v___y_1016_);
lean_dec(v_index_1019_);
v_map_928_ = v___x_1021_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_index_1022_; 
v_index_1022_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_index_1022_);
lean_dec_ref_known(v___x_1018_, 1);
v___y_1006_ = v___x_1017_;
v___y_1007_ = v___y_1015_;
v___y_1008_ = v___y_1016_;
v_i_1009_ = v_index_1022_;
goto v___jp_1005_;
}
default: 
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1017_, v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_index_1025_; 
v_index_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_index_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___y_1006_ = v___x_1017_;
v___y_1007_ = v___y_1015_;
v___y_1008_ = v___y_1016_;
v_i_1009_ = v_index_1025_;
goto v___jp_1005_;
}
else
{
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
v_map_928_ = v___x_1017_;
v_candidates_929_ = v_fst_922_;
goto v___jp_927_;
}
}
}
}
}
}
}
v___jp_909_:
{
size_t v___x_911_; size_t v___x_912_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_896_, v___x_911_);
v_i_896_ = v___x_912_;
v_b_897_ = v_a_910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(lean_object** _args){
lean_object* v_e_1175_ = _args[0];
lean_object* v_ctx_1176_ = _args[1];
lean_object* v___x_1177_ = _args[2];
lean_object* v_as_1178_ = _args[3];
lean_object* v_sz_1179_ = _args[4];
lean_object* v_i_1180_ = _args[5];
lean_object* v_b_1181_ = _args[6];
lean_object* v___y_1182_ = _args[7];
lean_object* v___y_1183_ = _args[8];
lean_object* v___y_1184_ = _args[9];
lean_object* v___y_1185_ = _args[10];
lean_object* v___y_1186_ = _args[11];
lean_object* v___y_1187_ = _args[12];
lean_object* v___y_1188_ = _args[13];
lean_object* v___y_1189_ = _args[14];
lean_object* v___y_1190_ = _args[15];
lean_object* v___y_1191_ = _args[16];
lean_object* v___y_1192_ = _args[17];
_start:
{
size_t v_sz_boxed_1193_; size_t v_i_boxed_1194_; lean_object* v_res_1195_; 
v_sz_boxed_1193_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1194_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_e_1175_, v_ctx_1176_, v___x_1177_, v_as_1178_, v_sz_boxed_1193_, v_i_boxed_1194_, v_b_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_as_1178_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24(lean_object* v_ctx_1196_, lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_ctx_1196_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_b_1200_);
return v___x_1213_;
}
else
{
lean_object* v_snd_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1315_; 
v_snd_1214_ = lean_ctor_get(v_b_1200_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_b_1200_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_b_1200_, 0);
lean_dec(v_unused_1316_);
v___x_1216_ = v_b_1200_;
v_isShared_1217_ = v_isSharedCheck_1315_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snd_1214_);
lean_dec(v_b_1200_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1315_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1314_; 
v_fst_1218_ = lean_ctor_get(v_snd_1214_, 0);
v_snd_1219_ = lean_ctor_get(v_snd_1214_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_snd_1214_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1221_ = v_snd_1214_;
v_isShared_1222_ = v_isSharedCheck_1314_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_inc(v_fst_1218_);
lean_dec(v_snd_1214_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1314_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v_a_1225_; lean_object* v_a_1238_; uint8_t v___y_1240_; uint8_t v___x_1312_; 
v___x_1223_ = lean_box(0);
v_a_1238_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
v___x_1312_ = l_Lean_Expr_isApp(v_a_1238_);
if (v___x_1312_ == 0)
{
v___y_1240_ = v___x_1312_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_Expr_isEq(v_a_1238_);
if (v___x_1313_ == 0)
{
v___y_1240_ = v___x_1312_;
goto v___jp_1239_;
}
else
{
goto v___jp_1232_;
}
}
v___jp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_a_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1227_ = v___x_1221_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_a_1225_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1199_, v___x_1228_);
v_i_1199_ = v___x_1229_;
v_b_1200_ = v___x_1227_;
goto _start;
}
}
v___jp_1232_:
{
lean_object* v___x_1234_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_snd_1219_);
lean_ctor_set(v___x_1216_, 0, v_fst_1218_);
v___x_1234_ = v___x_1216_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fst_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_snd_1219_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v_a_1225_ = v___x_1234_;
goto v___jp_1224_;
}
}
v___jp_1236_:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_fst_1218_);
lean_ctor_set(v___x_1237_, 1, v_snd_1219_);
v_a_1225_ = v___x_1237_;
goto v___jp_1224_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
goto v___jp_1232_;
}
else
{
uint8_t v___x_1241_; 
v___x_1241_ = l_Lean_Expr_isHEq(v_a_1238_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_del_object(v___x_1216_);
lean_inc(v_a_1238_);
v___x_1242_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1238_, v___y_1201_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; uint8_t v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = lean_unbox(v_a_1243_);
lean_dec(v_a_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_fst_1218_);
lean_ctor_set(v___x_1245_, 1, v_snd_1219_);
v_a_1225_ = v___x_1245_;
goto v___jp_1224_;
}
else
{
lean_object* v_isInterpreted_1246_; lean_object* v___x_1247_; 
v_isInterpreted_1246_ = lean_ctor_get(v_ctx_1196_, 0);
lean_inc_ref(v_isInterpreted_1246_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc(v_a_1238_);
v___x_1247_ = lean_apply_12(v_isInterpreted_1246_, v_a_1238_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, lean_box(0));
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; uint8_t v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = lean_unbox(v_a_1248_);
lean_dec(v_a_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = l_Lean_Expr_getAppFn(v_a_1238_);
lean_inc_ref(v___x_1250_);
v___x_1251_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1250_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; uint8_t v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_unbox(v_a_1252_);
lean_dec(v_a_1252_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1250_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v_dummy_1256_; lean_object* v_nargs_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1255_ = lean_unsigned_to_nat(0u);
v_dummy_1256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1257_ = l_Lean_Expr_getAppNumArgs(v_a_1238_);
lean_inc(v_nargs_1257_);
v___x_1258_ = lean_mk_array(v_nargs_1257_, v_dummy_1256_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v_nargs_1257_, v___x_1259_);
lean_dec(v_nargs_1257_);
lean_inc_n(v_a_1238_, 2);
v___x_1261_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1238_, v___x_1258_, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_snd_1219_);
lean_ctor_set(v___x_1262_, 1, v___x_1255_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_fst_1218_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v_sz_1264_ = lean_array_size(v___x_1261_);
v___x_1265_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1196_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_a_1238_, v_ctx_1196_, v___x_1250_, v___x_1261_, v_sz_1264_, v___x_1265_, v___x_1263_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec_ref(v___x_1261_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_snd_1268_; lean_object* v_fst_1269_; lean_object* v_fst_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_snd_1268_ = lean_ctor_get(v_a_1267_, 1);
lean_inc(v_snd_1268_);
v_fst_1269_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_fst_1269_);
lean_dec(v_a_1267_);
v_fst_1270_ = lean_ctor_get(v_snd_1268_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_snd_1268_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_snd_1268_, 1);
lean_dec(v_unused_1278_);
v___x_1272_ = v_snd_1268_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_fst_1270_);
lean_dec(v_snd_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_fst_1270_);
lean_ctor_set(v___x_1272_, 0, v_fst_1269_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_fst_1269_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_fst_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v_a_1225_ = v___x_1275_;
goto v___jp_1224_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1221_);
lean_dec_ref(v_ctx_1196_);
v_a_1279_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1266_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1266_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_dec_ref(v___x_1250_);
goto v___jp_1236_;
}
}
else
{
lean_dec_ref(v___x_1250_);
goto v___jp_1236_;
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v___x_1250_);
lean_del_object(v___x_1221_);
lean_dec(v_snd_1219_);
lean_dec(v_fst_1218_);
lean_dec_ref(v_ctx_1196_);
v_a_1287_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1251_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1251_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_fst_1218_);
lean_ctor_set(v___x_1295_, 1, v_snd_1219_);
v_a_1225_ = v___x_1295_;
goto v___jp_1224_;
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1221_);
lean_dec(v_snd_1219_);
lean_dec(v_fst_1218_);
lean_dec_ref(v_ctx_1196_);
v_a_1296_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1247_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1247_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_del_object(v___x_1221_);
lean_dec(v_snd_1219_);
lean_dec(v_fst_1218_);
lean_dec_ref(v_ctx_1196_);
v_a_1304_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1242_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1242_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
goto v___jp_1232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24___boxed(lean_object* v_ctx_1317_, lean_object* v_as_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
size_t v_sz_boxed_1333_; size_t v_i_boxed_1334_; lean_object* v_res_1335_; 
v_sz_boxed_1333_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1334_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24(v_ctx_1317_, v_as_1318_, v_sz_boxed_1333_, v_i_boxed_1334_, v_b_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v_as_1318_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19(lean_object* v_ctx_1336_, lean_object* v_as_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec_ref(v_ctx_1336_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_b_1340_);
return v___x_1353_;
}
else
{
lean_object* v_snd_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1455_; 
v_snd_1354_ = lean_ctor_get(v_b_1340_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_b_1340_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v_b_1340_, 0);
lean_dec(v_unused_1456_);
v___x_1356_ = v_b_1340_;
v_isShared_1357_ = v_isSharedCheck_1455_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_snd_1354_);
lean_dec(v_b_1340_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1455_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1454_; 
v_fst_1358_ = lean_ctor_get(v_snd_1354_, 0);
v_snd_1359_ = lean_ctor_get(v_snd_1354_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_snd_1354_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1361_ = v_snd_1354_;
v_isShared_1362_ = v_isSharedCheck_1454_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1358_);
lean_dec(v_snd_1354_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1454_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v_a_1365_; lean_object* v_a_1378_; uint8_t v___y_1380_; uint8_t v___x_1452_; 
v___x_1363_ = lean_box(0);
v_a_1378_ = lean_array_uget_borrowed(v_as_1337_, v_i_1339_);
v___x_1452_ = l_Lean_Expr_isApp(v_a_1378_);
if (v___x_1452_ == 0)
{
v___y_1380_ = v___x_1452_;
goto v___jp_1379_;
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = l_Lean_Expr_isEq(v_a_1378_);
if (v___x_1453_ == 0)
{
v___y_1380_ = v___x_1452_;
goto v___jp_1379_;
}
else
{
goto v___jp_1372_;
}
}
v___jp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v_a_1365_);
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1367_ = v___x_1361_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1365_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_add(v_i_1339_, v___x_1368_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19_spec__24(v_ctx_1336_, v_as_1337_, v_sz_1338_, v___x_1369_, v___x_1367_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1370_;
}
}
v___jp_1372_:
{
lean_object* v___x_1374_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_snd_1359_);
lean_ctor_set(v___x_1356_, 0, v_fst_1358_);
v___x_1374_ = v___x_1356_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_snd_1359_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
v_a_1365_ = v___x_1374_;
goto v___jp_1364_;
}
}
v___jp_1376_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_fst_1358_);
lean_ctor_set(v___x_1377_, 1, v_snd_1359_);
v_a_1365_ = v___x_1377_;
goto v___jp_1364_;
}
v___jp_1379_:
{
if (v___y_1380_ == 0)
{
goto v___jp_1372_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Lean_Expr_isHEq(v_a_1378_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_del_object(v___x_1356_);
lean_inc(v_a_1378_);
v___x_1382_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1378_, v___y_1341_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; uint8_t v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = lean_unbox(v_a_1383_);
lean_dec(v_a_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_fst_1358_);
lean_ctor_set(v___x_1385_, 1, v_snd_1359_);
v_a_1365_ = v___x_1385_;
goto v___jp_1364_;
}
else
{
lean_object* v_isInterpreted_1386_; lean_object* v___x_1387_; 
v_isInterpreted_1386_ = lean_ctor_get(v_ctx_1336_, 0);
lean_inc_ref(v_isInterpreted_1386_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc(v_a_1378_);
v___x_1387_ = lean_apply_12(v_isInterpreted_1386_, v_a_1378_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, lean_box(0));
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; uint8_t v___x_1389_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = lean_unbox(v_a_1388_);
lean_dec(v_a_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = l_Lean_Expr_getAppFn(v_a_1378_);
lean_inc_ref(v___x_1390_);
v___x_1391_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1390_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = lean_unbox(v_a_1392_);
lean_dec(v_a_1392_);
if (v___x_1393_ == 0)
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1390_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v_dummy_1396_; lean_object* v_nargs_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; size_t v_sz_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v_dummy_1396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1397_ = l_Lean_Expr_getAppNumArgs(v_a_1378_);
lean_inc(v_nargs_1397_);
v___x_1398_ = lean_mk_array(v_nargs_1397_, v_dummy_1396_);
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_sub(v_nargs_1397_, v___x_1399_);
lean_dec(v_nargs_1397_);
lean_inc_n(v_a_1378_, 2);
v___x_1401_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1378_, v___x_1398_, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_snd_1359_);
lean_ctor_set(v___x_1402_, 1, v___x_1395_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_fst_1358_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v_sz_1404_ = lean_array_size(v___x_1401_);
v___x_1405_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1336_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_a_1378_, v_ctx_1336_, v___x_1390_, v___x_1401_, v_sz_1404_, v___x_1405_, v___x_1403_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec_ref(v___x_1401_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_snd_1408_; lean_object* v_fst_1409_; lean_object* v_fst_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v_snd_1408_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_snd_1408_);
v_fst_1409_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_fst_1409_);
lean_dec(v_a_1407_);
v_fst_1410_ = lean_ctor_get(v_snd_1408_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_snd_1408_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_snd_1408_, 1);
lean_dec(v_unused_1418_);
v___x_1412_ = v_snd_1408_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_fst_1410_);
lean_dec(v_snd_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_fst_1410_);
lean_ctor_set(v___x_1412_, 0, v_fst_1409_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fst_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_fst_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v_a_1365_ = v___x_1415_;
goto v___jp_1364_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1361_);
lean_dec_ref(v_ctx_1336_);
v_a_1419_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1406_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1406_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1376_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v___x_1390_);
lean_del_object(v___x_1361_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec_ref(v_ctx_1336_);
v_a_1427_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1391_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1391_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_fst_1358_);
lean_ctor_set(v___x_1435_, 1, v_snd_1359_);
v_a_1365_ = v___x_1435_;
goto v___jp_1364_;
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1361_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec_ref(v_ctx_1336_);
v_a_1436_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1387_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1387_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_del_object(v___x_1361_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec_ref(v_ctx_1336_);
v_a_1444_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1382_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1382_);
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
goto v___jp_1372_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19___boxed(lean_object* v_ctx_1457_, lean_object* v_as_1458_, lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19(v_ctx_1457_, v_as_1458_, v_sz_boxed_1473_, v_i_boxed_1474_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v_as_1458_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15(lean_object* v_init_1476_, lean_object* v_ctx_1477_, lean_object* v_n_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
if (lean_obj_tag(v_n_1478_) == 0)
{
lean_object* v_cs_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; size_t v_sz_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v_cs_1491_ = lean_ctor_get(v_n_1478_, 0);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_b_1479_);
v_sz_1494_ = lean_array_size(v_cs_1491_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18(v_init_1476_, v_ctx_1477_, v_cs_1491_, v_sz_1494_, v___x_1495_, v___x_1493_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1511_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_fst_1501_; 
v_fst_1501_ = lean_ctor_get(v_a_1497_, 0);
if (lean_obj_tag(v_fst_1501_) == 0)
{
lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v_snd_1502_ = lean_ctor_get(v_a_1497_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_a_1497_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_snd_1502_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1505_ = v___x_1499_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
else
{
lean_object* v_val_1507_; lean_object* v___x_1509_; 
lean_inc_ref(v_fst_1501_);
lean_dec(v_a_1497_);
v_val_1507_ = lean_ctor_get(v_fst_1501_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v_fst_1501_, 1);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v_val_1507_);
v___x_1509_ = v___x_1499_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_val_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1496_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1496_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_vs_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; size_t v_sz_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v_vs_1520_ = lean_ctor_get(v_n_1478_, 0);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v_b_1479_);
v_sz_1523_ = lean_array_size(v_vs_1520_);
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__19(v_ctx_1477_, v_vs_1520_, v_sz_1523_, v___x_1524_, v___x_1522_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1540_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1540_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1540_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_fst_1530_; 
v_fst_1530_ = lean_ctor_get(v_a_1526_, 0);
if (lean_obj_tag(v_fst_1530_) == 0)
{
lean_object* v_snd_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v_snd_1531_ = lean_ctor_get(v_a_1526_, 1);
lean_inc(v_snd_1531_);
lean_dec(v_a_1526_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_snd_1531_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1532_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
else
{
lean_object* v_val_1536_; lean_object* v___x_1538_; 
lean_inc_ref(v_fst_1530_);
lean_dec(v_a_1526_);
v_val_1536_ = lean_ctor_get(v_fst_1530_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v_fst_1530_, 1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v_val_1536_);
v___x_1538_ = v___x_1528_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_val_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1525_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1525_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18(lean_object* v_init_1549_, lean_object* v_ctx_1550_, lean_object* v_as_1551_, size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_b_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec_ref(v_ctx_1550_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_b_1554_);
return v___x_1567_;
}
else
{
lean_object* v_snd_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1602_; 
v_snd_1568_ = lean_ctor_get(v_b_1554_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_b_1554_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_b_1554_, 0);
lean_dec(v_unused_1603_);
v___x_1570_ = v_b_1554_;
v_isShared_1571_ = v_isSharedCheck_1602_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snd_1568_);
lean_dec(v_b_1554_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1602_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_array_uget_borrowed(v_as_1551_, v_i_1553_);
lean_inc(v_snd_1568_);
lean_inc_ref(v_ctx_1550_);
v___x_1573_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15(v_init_1549_, v_ctx_1550_, v_a_1572_, v_snd_1568_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1593_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
if (lean_obj_tag(v_a_1574_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec_ref(v_ctx_1550_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_a_1574_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1578_);
v___x_1580_ = v___x_1570_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_snd_1568_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1580_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_del_object(v___x_1576_);
lean_dec(v_snd_1568_);
v_a_1585_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v_a_1574_, 1);
v___x_1586_ = lean_box(0);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_a_1585_);
lean_ctor_set(v___x_1570_, 0, v___x_1586_);
v___x_1588_ = v___x_1570_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1585_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
size_t v___x_1589_; size_t v___x_1590_; 
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1553_, v___x_1589_);
v_i_1553_ = v___x_1590_;
v_b_1554_ = v___x_1588_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_del_object(v___x_1570_);
lean_dec(v_snd_1568_);
lean_dec_ref(v_ctx_1550_);
v_a_1594_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1573_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1573_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18___boxed(lean_object** _args){
lean_object* v_init_1604_ = _args[0];
lean_object* v_ctx_1605_ = _args[1];
lean_object* v_as_1606_ = _args[2];
lean_object* v_sz_1607_ = _args[3];
lean_object* v_i_1608_ = _args[4];
lean_object* v_b_1609_ = _args[5];
lean_object* v___y_1610_ = _args[6];
lean_object* v___y_1611_ = _args[7];
lean_object* v___y_1612_ = _args[8];
lean_object* v___y_1613_ = _args[9];
lean_object* v___y_1614_ = _args[10];
lean_object* v___y_1615_ = _args[11];
lean_object* v___y_1616_ = _args[12];
lean_object* v___y_1617_ = _args[13];
lean_object* v___y_1618_ = _args[14];
lean_object* v___y_1619_ = _args[15];
lean_object* v___y_1620_ = _args[16];
_start:
{
size_t v_sz_boxed_1621_; size_t v_i_boxed_1622_; lean_object* v_res_1623_; 
v_sz_boxed_1621_ = lean_unbox_usize(v_sz_1607_);
lean_dec(v_sz_1607_);
v_i_boxed_1622_ = lean_unbox_usize(v_i_1608_);
lean_dec(v_i_1608_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15_spec__18(v_init_1604_, v_ctx_1605_, v_as_1606_, v_sz_boxed_1621_, v_i_boxed_1622_, v_b_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v_as_1606_);
lean_dec_ref(v_init_1604_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15___boxed(lean_object* v_init_1624_, lean_object* v_ctx_1625_, lean_object* v_n_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15(v_init_1624_, v_ctx_1625_, v_n_1626_, v_b_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v_n_1626_);
lean_dec_ref(v_init_1624_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21(lean_object* v_ctx_1640_, lean_object* v_as_1641_, size_t v_sz_1642_, size_t v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_usize_dec_lt(v_i_1643_, v_sz_1642_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v_ctx_1640_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_b_1644_);
return v___x_1657_;
}
else
{
lean_object* v_snd_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1759_; 
v_snd_1658_ = lean_ctor_get(v_b_1644_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_b_1644_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_b_1644_, 0);
lean_dec(v_unused_1760_);
v___x_1660_ = v_b_1644_;
v_isShared_1661_ = v_isSharedCheck_1759_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_snd_1658_);
lean_dec(v_b_1644_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1759_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1758_; 
v_fst_1662_ = lean_ctor_get(v_snd_1658_, 0);
v_snd_1663_ = lean_ctor_get(v_snd_1658_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_snd_1658_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1665_ = v_snd_1658_;
v_isShared_1666_ = v_isSharedCheck_1758_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_snd_1663_);
lean_inc(v_fst_1662_);
lean_dec(v_snd_1658_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1758_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v_a_1669_; lean_object* v_a_1682_; uint8_t v___y_1684_; uint8_t v___x_1756_; 
v___x_1667_ = lean_box(0);
v_a_1682_ = lean_array_uget_borrowed(v_as_1641_, v_i_1643_);
v___x_1756_ = l_Lean_Expr_isApp(v_a_1682_);
if (v___x_1756_ == 0)
{
v___y_1684_ = v___x_1756_;
goto v___jp_1683_;
}
else
{
uint8_t v___x_1757_; 
v___x_1757_ = l_Lean_Expr_isEq(v_a_1682_);
if (v___x_1757_ == 0)
{
v___y_1684_ = v___x_1756_;
goto v___jp_1683_;
}
else
{
goto v___jp_1676_;
}
}
v___jp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v_a_1669_);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1669_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
size_t v___x_1672_; size_t v___x_1673_; 
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1643_, v___x_1672_);
v_i_1643_ = v___x_1673_;
v_b_1644_ = v___x_1671_;
goto _start;
}
}
v___jp_1676_:
{
lean_object* v___x_1678_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_snd_1663_);
lean_ctor_set(v___x_1660_, 0, v_fst_1662_);
v___x_1678_ = v___x_1660_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_fst_1662_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_snd_1663_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v_a_1669_ = v___x_1678_;
goto v___jp_1668_;
}
}
v___jp_1680_:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_fst_1662_);
lean_ctor_set(v___x_1681_, 1, v_snd_1663_);
v_a_1669_ = v___x_1681_;
goto v___jp_1668_;
}
v___jp_1683_:
{
if (v___y_1684_ == 0)
{
goto v___jp_1676_;
}
else
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Lean_Expr_isHEq(v_a_1682_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_del_object(v___x_1660_);
lean_inc(v_a_1682_);
v___x_1686_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1682_, v___y_1645_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_fst_1662_);
lean_ctor_set(v___x_1689_, 1, v_snd_1663_);
v_a_1669_ = v___x_1689_;
goto v___jp_1668_;
}
else
{
lean_object* v_isInterpreted_1690_; lean_object* v___x_1691_; 
v_isInterpreted_1690_ = lean_ctor_get(v_ctx_1640_, 0);
lean_inc_ref(v_isInterpreted_1690_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc(v_a_1682_);
v___x_1691_ = lean_apply_12(v_isInterpreted_1690_, v_a_1682_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, lean_box(0));
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = l_Lean_Expr_getAppFn(v_a_1682_);
lean_inc_ref(v___x_1694_);
v___x_1695_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1694_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1697_ = lean_unbox(v_a_1696_);
lean_dec(v_a_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1694_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v_dummy_1700_; lean_object* v_nargs_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1699_ = lean_unsigned_to_nat(0u);
v_dummy_1700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1701_ = l_Lean_Expr_getAppNumArgs(v_a_1682_);
lean_inc(v_nargs_1701_);
v___x_1702_ = lean_mk_array(v_nargs_1701_, v_dummy_1700_);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_sub(v_nargs_1701_, v___x_1703_);
lean_dec(v_nargs_1701_);
lean_inc_n(v_a_1682_, 2);
v___x_1705_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1682_, v___x_1702_, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_snd_1663_);
lean_ctor_set(v___x_1706_, 1, v___x_1699_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_fst_1662_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v_sz_1708_ = lean_array_size(v___x_1705_);
v___x_1709_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1640_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_a_1682_, v_ctx_1640_, v___x_1694_, v___x_1705_, v_sz_1708_, v___x_1709_, v___x_1707_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec_ref(v___x_1705_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v_snd_1712_; lean_object* v_fst_1713_; lean_object* v_fst_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v_snd_1712_ = lean_ctor_get(v_a_1711_, 1);
lean_inc(v_snd_1712_);
v_fst_1713_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_fst_1713_);
lean_dec(v_a_1711_);
v_fst_1714_ = lean_ctor_get(v_snd_1712_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_snd_1712_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_snd_1712_, 1);
lean_dec(v_unused_1722_);
v___x_1716_ = v_snd_1712_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_fst_1714_);
lean_dec(v_snd_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v_fst_1714_);
lean_ctor_set(v___x_1716_, 0, v_fst_1713_);
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1713_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_fst_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
v_a_1669_ = v___x_1719_;
goto v___jp_1668_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_del_object(v___x_1665_);
lean_dec_ref(v_ctx_1640_);
v_a_1723_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1710_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1710_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_dec_ref(v___x_1694_);
goto v___jp_1680_;
}
}
else
{
lean_dec_ref(v___x_1694_);
goto v___jp_1680_;
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___x_1694_);
lean_del_object(v___x_1665_);
lean_dec(v_snd_1663_);
lean_dec(v_fst_1662_);
lean_dec_ref(v_ctx_1640_);
v_a_1731_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1695_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1695_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_fst_1662_);
lean_ctor_set(v___x_1739_, 1, v_snd_1663_);
v_a_1669_ = v___x_1739_;
goto v___jp_1668_;
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_del_object(v___x_1665_);
lean_dec(v_snd_1663_);
lean_dec(v_fst_1662_);
lean_dec_ref(v_ctx_1640_);
v_a_1740_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1691_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1691_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_del_object(v___x_1665_);
lean_dec(v_snd_1663_);
lean_dec(v_fst_1662_);
lean_dec_ref(v_ctx_1640_);
v_a_1748_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1686_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1686_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
goto v___jp_1676_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21___boxed(lean_object* v_ctx_1761_, lean_object* v_as_1762_, lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
size_t v_sz_boxed_1777_; size_t v_i_boxed_1778_; lean_object* v_res_1779_; 
v_sz_boxed_1777_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1778_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21(v_ctx_1761_, v_as_1762_, v_sz_boxed_1777_, v_i_boxed_1778_, v_b_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_as_1762_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16(lean_object* v_ctx_1780_, lean_object* v_as_1781_, size_t v_sz_1782_, size_t v_i_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_lt(v_i_1783_, v_sz_1782_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v_ctx_1780_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_b_1784_);
return v___x_1797_;
}
else
{
lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1899_; 
v_snd_1798_ = lean_ctor_get(v_b_1784_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_b_1784_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_b_1784_, 0);
lean_dec(v_unused_1900_);
v___x_1800_ = v_b_1784_;
v_isShared_1801_ = v_isSharedCheck_1899_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_dec(v_b_1784_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1899_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_fst_1802_; lean_object* v_snd_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1898_; 
v_fst_1802_ = lean_ctor_get(v_snd_1798_, 0);
v_snd_1803_ = lean_ctor_get(v_snd_1798_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_snd_1798_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1805_ = v_snd_1798_;
v_isShared_1806_ = v_isSharedCheck_1898_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_snd_1803_);
lean_inc(v_fst_1802_);
lean_dec(v_snd_1798_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1898_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_a_1809_; lean_object* v_a_1822_; uint8_t v___y_1824_; uint8_t v___x_1896_; 
v___x_1807_ = lean_box(0);
v_a_1822_ = lean_array_uget_borrowed(v_as_1781_, v_i_1783_);
v___x_1896_ = l_Lean_Expr_isApp(v_a_1822_);
if (v___x_1896_ == 0)
{
v___y_1824_ = v___x_1896_;
goto v___jp_1823_;
}
else
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_Expr_isEq(v_a_1822_);
if (v___x_1897_ == 0)
{
v___y_1824_ = v___x_1896_;
goto v___jp_1823_;
}
else
{
goto v___jp_1816_;
}
}
v___jp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v_a_1809_);
lean_ctor_set(v___x_1805_, 0, v___x_1807_);
v___x_1811_ = v___x_1805_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1809_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_add(v_i_1783_, v___x_1812_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16_spec__21(v_ctx_1780_, v_as_1781_, v_sz_1782_, v___x_1813_, v___x_1811_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1814_;
}
}
v___jp_1816_:
{
lean_object* v___x_1818_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v_snd_1803_);
lean_ctor_set(v___x_1800_, 0, v_fst_1802_);
v___x_1818_ = v___x_1800_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_fst_1802_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_snd_1803_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v_a_1809_ = v___x_1818_;
goto v___jp_1808_;
}
}
v___jp_1820_:
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_fst_1802_);
lean_ctor_set(v___x_1821_, 1, v_snd_1803_);
v_a_1809_ = v___x_1821_;
goto v___jp_1808_;
}
v___jp_1823_:
{
if (v___y_1824_ == 0)
{
goto v___jp_1816_;
}
else
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_Expr_isHEq(v_a_1822_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_del_object(v___x_1800_);
lean_inc(v_a_1822_);
v___x_1826_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_a_1822_, v___y_1785_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; uint8_t v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_unbox(v_a_1827_);
lean_dec(v_a_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_fst_1802_);
lean_ctor_set(v___x_1829_, 1, v_snd_1803_);
v_a_1809_ = v___x_1829_;
goto v___jp_1808_;
}
else
{
lean_object* v_isInterpreted_1830_; lean_object* v___x_1831_; 
v_isInterpreted_1830_ = lean_ctor_get(v_ctx_1780_, 0);
lean_inc_ref(v_isInterpreted_1830_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc(v___y_1785_);
lean_inc(v_a_1822_);
v___x_1831_ = lean_apply_12(v_isInterpreted_1830_, v_a_1822_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, lean_box(0));
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; uint8_t v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = l_Lean_Expr_getAppFn(v_a_1822_);
lean_inc_ref(v___x_1834_);
v___x_1835_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_1834_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_1834_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v_dummy_1840_; lean_object* v_nargs_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v_dummy_1840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0, &l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
v_nargs_1841_ = l_Lean_Expr_getAppNumArgs(v_a_1822_);
lean_inc(v_nargs_1841_);
v___x_1842_ = lean_mk_array(v_nargs_1841_, v_dummy_1840_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_sub(v_nargs_1841_, v___x_1843_);
lean_dec(v_nargs_1841_);
lean_inc_n(v_a_1822_, 2);
v___x_1845_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1822_, v___x_1842_, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_snd_1803_);
lean_ctor_set(v___x_1846_, 1, v___x_1839_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_fst_1802_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v_sz_1848_ = lean_array_size(v___x_1845_);
v___x_1849_ = ((size_t)0ULL);
lean_inc_ref(v_ctx_1780_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8(v_a_1822_, v_ctx_1780_, v___x_1834_, v___x_1845_, v_sz_1848_, v___x_1849_, v___x_1847_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v___x_1845_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_snd_1852_; lean_object* v_fst_1853_; lean_object* v_fst_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v_snd_1852_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1852_);
v_fst_1853_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_fst_1853_);
lean_dec(v_a_1851_);
v_fst_1854_ = lean_ctor_get(v_snd_1852_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_snd_1852_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v_snd_1852_, 1);
lean_dec(v_unused_1862_);
v___x_1856_ = v_snd_1852_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_fst_1854_);
lean_dec(v_snd_1852_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v_fst_1854_);
lean_ctor_set(v___x_1856_, 0, v_fst_1853_);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_fst_1853_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_fst_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v_a_1809_ = v___x_1859_;
goto v___jp_1808_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1805_);
lean_dec_ref(v_ctx_1780_);
v_a_1863_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1850_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1850_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_dec_ref(v___x_1834_);
goto v___jp_1820_;
}
}
else
{
lean_dec_ref(v___x_1834_);
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1834_);
lean_del_object(v___x_1805_);
lean_dec(v_snd_1803_);
lean_dec(v_fst_1802_);
lean_dec_ref(v_ctx_1780_);
v_a_1871_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1835_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1835_);
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
else
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_fst_1802_);
lean_ctor_set(v___x_1879_, 1, v_snd_1803_);
v_a_1809_ = v___x_1879_;
goto v___jp_1808_;
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_del_object(v___x_1805_);
lean_dec(v_snd_1803_);
lean_dec(v_fst_1802_);
lean_dec_ref(v_ctx_1780_);
v_a_1880_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1831_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1831_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1805_);
lean_dec(v_snd_1803_);
lean_dec(v_fst_1802_);
lean_dec_ref(v_ctx_1780_);
v_a_1888_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1826_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1826_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
goto v___jp_1816_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16___boxed(lean_object* v_ctx_1901_, lean_object* v_as_1902_, lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16(v_ctx_1901_, v_as_1902_, v_sz_boxed_1917_, v_i_boxed_1918_, v_b_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v_as_1902_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9(lean_object* v_ctx_1920_, lean_object* v_t_1921_, lean_object* v_init_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_root_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; 
v_root_1934_ = lean_ctor_get(v_t_1921_, 0);
v_tail_1935_ = lean_ctor_get(v_t_1921_, 1);
lean_inc_ref(v_ctx_1920_);
lean_inc_ref(v_init_1922_);
v___x_1936_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__15(v_init_1922_, v_ctx_1920_, v_root_1934_, v_init_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec_ref(v_init_1922_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1973_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1973_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1973_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
if (lean_obj_tag(v_a_1937_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; 
lean_dec_ref(v_ctx_1920_);
v_a_1941_ = lean_ctor_get(v_a_1937_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v_a_1937_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_a_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; size_t v_sz_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
lean_del_object(v___x_1939_);
v_a_1945_ = lean_ctor_get(v_a_1937_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v_a_1937_, 1);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_a_1945_);
v_sz_1948_ = lean_array_size(v_tail_1935_);
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9_spec__16(v_ctx_1920_, v_tail_1935_, v_sz_1948_, v___x_1949_, v___x_1947_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1964_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v_fst_1955_; 
v_fst_1955_ = lean_ctor_get(v_a_1951_, 0);
if (lean_obj_tag(v_fst_1955_) == 0)
{
lean_object* v_snd_1956_; lean_object* v___x_1958_; 
v_snd_1956_ = lean_ctor_get(v_a_1951_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_snd_1956_);
v___x_1958_ = v___x_1953_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_snd_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
else
{
lean_object* v_val_1960_; lean_object* v___x_1962_; 
lean_inc_ref(v_fst_1955_);
lean_dec(v_a_1951_);
v_val_1960_ = lean_ctor_get(v_fst_1955_, 0);
lean_inc(v_val_1960_);
lean_dec_ref_known(v_fst_1955_, 1);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_val_1960_);
v___x_1962_ = v___x_1953_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_val_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1950_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1950_);
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
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_ctx_1920_);
v_a_1974_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1936_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1936_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(lean_object* v_ctx_1982_, lean_object* v_t_1983_, lean_object* v_init_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9(v_ctx_1982_, v_t_1983_, v_init_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v_t_1983_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12(lean_object* v_as_1997_, size_t v_sz_1998_, size_t v_i_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_1999_, v_sz_1998_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_2000_);
return v___x_2013_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_array_uget_borrowed(v_as_1997_, v_i_1999_);
lean_inc(v_a_2014_);
v___x_2015_ = l_Lean_Meta_Grind_addSplitCandidate(v_a_2014_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
lean_dec_ref_known(v___x_2015_, 1);
v___x_2016_ = lean_box(0);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_1999_, v___x_2017_);
v_i_1999_ = v___x_2018_;
v_b_2000_ = v___x_2016_;
goto _start;
}
else
{
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
size_t v_sz_boxed_2035_; size_t v_i_boxed_2036_; lean_object* v_res_2037_; 
v_sz_boxed_2035_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2036_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_2020_, v_sz_boxed_2035_, v_i_boxed_2036_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v_as_2020_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18(lean_object* v_b_2038_, lean_object* v_acc_2039_, lean_object* v_i_2040_){
_start:
{
lean_object* v_keyArray_2045_; lean_object* v_valueArray_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_keyArray_2045_ = lean_ctor_get(v_b_2038_, 1);
v_valueArray_2046_ = lean_ctor_get(v_b_2038_, 2);
v___x_2047_ = lean_array_get_size(v_keyArray_2045_);
v___x_2048_ = lean_nat_dec_lt(v_i_2040_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_dec(v_i_2040_);
return v_acc_2039_;
}
else
{
lean_object* v___x_2049_; uint8_t v_isSome_2050_; 
v___x_2049_ = lean_array_fget_borrowed(v_keyArray_2045_, v_i_2040_);
v_isSome_2050_ = lean_noption_is_some(v___x_2049_);
if (v_isSome_2050_ == 0)
{
goto v___jp_2041_;
}
else
{
lean_object* v___x_2051_; uint8_t v_isSome_2052_; 
v___x_2051_ = lean_array_fget_borrowed(v_valueArray_2046_, v_i_2040_);
v_isSome_2052_ = lean_noption_is_some(v___x_2051_);
if (v_isSome_2052_ == 0)
{
goto v___jp_2041_;
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_inc(v___x_2049_);
v_val_2053_ = lean_noption_get(v___x_2049_);
v___x_2054_ = lean_array_push(v_acc_2039_, v_val_2053_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_i_2040_, v___x_2055_);
lean_dec(v_i_2040_);
v_acc_2039_ = v___x_2054_;
v_i_2040_ = v___x_2056_;
goto _start;
}
}
}
v___jp_2041_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_nat_add(v_i_2040_, v___x_2042_);
lean_dec(v_i_2040_);
v_i_2040_ = v___x_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18___boxed(lean_object* v_b_2058_, lean_object* v_acc_2059_, lean_object* v_i_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18(v_b_2058_, v_acc_2059_, v_i_2060_);
lean_dec_ref(v_b_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10(lean_object* v_init_2062_, lean_object* v_b_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10_spec__18(v_b_2063_, v_init_2062_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(lean_object* v_init_2066_, lean_object* v_b_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10(v_init_2066_, v_b_2067_);
lean_dec_ref(v_b_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg(lean_object* v_hi_2069_, lean_object* v_pivot_2070_, lean_object* v_as_2071_, lean_object* v_i_2072_, lean_object* v_k_2073_){
_start:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_nat_dec_lt(v_k_2073_, v_hi_2069_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_k_2073_);
v___x_2075_ = lean_array_fswap(v_as_2071_, v_i_2072_, v_hi_2069_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_i_2072_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_array_fget_borrowed(v_as_2071_, v_k_2073_);
v___x_2078_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2077_, v_pivot_2070_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_nat_add(v_k_2073_, v___x_2079_);
lean_dec(v_k_2073_);
v_k_2073_ = v___x_2080_;
goto _start;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = lean_array_fswap(v_as_2071_, v_i_2072_, v_k_2073_);
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_nat_add(v_i_2072_, v___x_2083_);
lean_dec(v_i_2072_);
v___x_2085_ = lean_nat_add(v_k_2073_, v___x_2083_);
lean_dec(v_k_2073_);
v_as_2071_ = v___x_2082_;
v_i_2072_ = v___x_2084_;
v_k_2073_ = v___x_2085_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg___boxed(lean_object* v_hi_2087_, lean_object* v_pivot_2088_, lean_object* v_as_2089_, lean_object* v_i_2090_, lean_object* v_k_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg(v_hi_2087_, v_pivot_2088_, v_as_2089_, v_i_2090_, v_k_2091_);
lean_dec_ref(v_pivot_2088_);
lean_dec(v_hi_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(lean_object* v_n_2093_, lean_object* v_as_2094_, lean_object* v_lo_2095_, lean_object* v_hi_2096_){
_start:
{
lean_object* v___y_2098_; uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_lt(v_lo_2095_, v_hi_2096_);
if (v___x_2108_ == 0)
{
lean_dec(v_lo_2095_);
return v_as_2094_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_mid_2111_; lean_object* v___y_2113_; lean_object* v___y_2119_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2109_ = lean_nat_add(v_lo_2095_, v_hi_2096_);
v___x_2110_ = lean_unsigned_to_nat(1u);
v_mid_2111_ = lean_nat_shiftr(v___x_2109_, v___x_2110_);
lean_dec(v___x_2109_);
v___x_2124_ = lean_array_fget_borrowed(v_as_2094_, v_mid_2111_);
v___x_2125_ = lean_array_fget_borrowed(v_as_2094_, v_lo_2095_);
v___x_2126_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
v___y_2119_ = v_as_2094_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_array_fswap(v_as_2094_, v_lo_2095_, v_mid_2111_);
v___y_2119_ = v___x_2127_;
goto v___jp_2118_;
}
v___jp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2114_ = lean_array_fget_borrowed(v___y_2113_, v_mid_2111_);
v___x_2115_ = lean_array_fget_borrowed(v___y_2113_, v_hi_2096_);
v___x_2116_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v_mid_2111_);
v___y_2098_ = v___y_2113_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_array_fswap(v___y_2113_, v_mid_2111_, v_hi_2096_);
lean_dec(v_mid_2111_);
v___y_2098_ = v___x_2117_;
goto v___jp_2097_;
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_array_fget_borrowed(v___y_2119_, v_hi_2096_);
v___x_2121_ = lean_array_fget_borrowed(v___y_2119_, v_lo_2095_);
v___x_2122_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
v___y_2113_ = v___y_2119_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_array_fswap(v___y_2119_, v_lo_2095_, v_hi_2096_);
v___y_2113_ = v___x_2123_;
goto v___jp_2112_;
}
}
}
v___jp_2097_:
{
lean_object* v_pivot_2099_; lean_object* v___x_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; uint8_t v___x_2103_; 
v_pivot_2099_ = lean_array_fget(v___y_2098_, v_hi_2096_);
lean_inc_n(v_lo_2095_, 2);
v___x_2100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg(v_hi_2096_, v_pivot_2099_, v___y_2098_, v_lo_2095_, v_lo_2095_);
lean_dec(v_pivot_2099_);
v_fst_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fst_2101_);
v_snd_2102_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_snd_2102_);
lean_dec_ref(v___x_2100_);
v___x_2103_ = lean_nat_dec_le(v_hi_2096_, v_fst_2101_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(v_n_2093_, v_snd_2102_, v_lo_2095_, v_fst_2101_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_fst_2101_, v___x_2105_);
lean_dec(v_fst_2101_);
v_as_2094_ = v___x_2104_;
v_lo_2095_ = v___x_2106_;
goto _start;
}
else
{
lean_dec(v_fst_2101_);
lean_dec(v_lo_2095_);
return v_snd_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg___boxed(lean_object* v_n_2128_, lean_object* v_as_2129_, lean_object* v_lo_2130_, lean_object* v_hi_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(v_n_2128_, v_as_2129_, v_lo_2130_, v_hi_2131_);
lean_dec(v_hi_2131_);
lean_dec(v_n_2128_);
return v_res_2132_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0));
v___x_2137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__8___closed__5));
v___x_2138_ = l_Lean_Name_append(v___x_2137_, v___x_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20(lean_object* v_as_2139_, size_t v_i_2140_, size_t v_stop_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_a_2155_; uint8_t v___x_2159_; 
v___x_2159_ = lean_usize_dec_eq(v_i_2140_, v_stop_2141_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_array_uget_borrowed(v_as_2139_, v_i_2140_);
v___x_2161_ = l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_2160_, v___y_2143_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; uint8_t v___x_2163_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = lean_unbox(v_a_2162_);
lean_dec(v_a_2162_);
if (v___x_2163_ == 0)
{
if (lean_obj_tag(v___x_2160_) == 2)
{
lean_object* v_a_2164_; lean_object* v_b_2165_; lean_object* v_eq_2166_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v_options_2222_; uint8_t v_hasTrace_2223_; 
v_a_2164_ = lean_ctor_get(v___x_2160_, 0);
v_b_2165_ = lean_ctor_get(v___x_2160_, 1);
v_eq_2166_ = lean_ctor_get(v___x_2160_, 3);
v_options_2222_ = lean_ctor_get(v___y_2151_, 2);
v_hasTrace_2223_ = lean_ctor_get_uint8(v_options_2222_, sizeof(void*)*1);
if (v_hasTrace_2223_ == 0)
{
v___y_2191_ = v___y_2143_;
v___y_2192_ = v___y_2144_;
v___y_2193_ = v___y_2145_;
v___y_2194_ = v___y_2146_;
v___y_2195_ = v___y_2147_;
v___y_2196_ = v___y_2148_;
v___y_2197_ = v___y_2149_;
v___y_2198_ = v___y_2150_;
v___y_2199_ = v___y_2151_;
v___y_2200_ = v___y_2152_;
goto v___jp_2190_;
}
else
{
lean_object* v_inheritedTraceOptions_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_inheritedTraceOptions_2224_ = lean_ctor_get(v___y_2151_, 13);
v___x_2225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__0));
v___x_2226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___closed__1);
v___x_2227_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2224_, v_options_2222_, v___x_2226_);
if (v___x_2227_ == 0)
{
v___y_2191_ = v___y_2143_;
v___y_2192_ = v___y_2144_;
v___y_2193_ = v___y_2145_;
v___y_2194_ = v___y_2146_;
v___y_2195_ = v___y_2147_;
v___y_2196_ = v___y_2148_;
v___y_2197_ = v___y_2149_;
v___y_2198_ = v___y_2150_;
v___y_2199_ = v___y_2151_;
v___y_2200_ = v___y_2152_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_inc_ref(v_eq_2166_);
v___x_2228_ = l_Lean_MessageData_ofExpr(v_eq_2166_);
v___x_2229_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_2225_, v___x_2228_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_dec_ref_known(v___x_2229_, 1);
v___y_2191_ = v___y_2143_;
v___y_2192_ = v___y_2144_;
v___y_2193_ = v___y_2145_;
v___y_2194_ = v___y_2146_;
v___y_2195_ = v___y_2147_;
v___y_2196_ = v___y_2148_;
v___y_2197_ = v___y_2149_;
v___y_2198_ = v___y_2150_;
v___y_2199_ = v___y_2151_;
v___y_2200_ = v___y_2152_;
goto v___jp_2190_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_b_2142_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
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
}
v___jp_2167_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_box(0);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2168_);
lean_inc(v___y_2172_);
lean_inc_ref(v___y_2176_);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2170_);
lean_inc(v___y_2174_);
lean_inc_ref(v___y_2169_);
lean_inc(v___y_2175_);
lean_inc(v___y_2177_);
lean_inc_ref(v_eq_2166_);
v___x_2180_ = lean_grind_internalize(v_eq_2166_, v___y_2178_, v___x_2179_, v___y_2177_, v___y_2175_, v___y_2169_, v___y_2174_, v___y_2170_, v___y_2173_, v___y_2176_, v___y_2172_, v___y_2168_, v___y_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v___x_2181_; 
lean_dec_ref_known(v___x_2180_, 1);
lean_inc_ref(v___x_2160_);
v___x_2181_ = lean_array_push(v_b_2142_, v___x_2160_);
v_a_2155_ = v___x_2181_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v_b_2142_);
v_a_2182_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2180_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2180_);
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
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2164_, v___y_2191_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_2165_, v___y_2191_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; uint8_t v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = lean_nat_dec_le(v_a_2202_, v_a_2204_);
if (v___x_2205_ == 0)
{
lean_dec(v_a_2204_);
v___y_2168_ = v___y_2199_;
v___y_2169_ = v___y_2193_;
v___y_2170_ = v___y_2195_;
v___y_2171_ = v___y_2200_;
v___y_2172_ = v___y_2198_;
v___y_2173_ = v___y_2196_;
v___y_2174_ = v___y_2194_;
v___y_2175_ = v___y_2192_;
v___y_2176_ = v___y_2197_;
v___y_2177_ = v___y_2191_;
v___y_2178_ = v_a_2202_;
goto v___jp_2167_;
}
else
{
lean_dec(v_a_2202_);
v___y_2168_ = v___y_2199_;
v___y_2169_ = v___y_2193_;
v___y_2170_ = v___y_2195_;
v___y_2171_ = v___y_2200_;
v___y_2172_ = v___y_2198_;
v___y_2173_ = v___y_2196_;
v___y_2174_ = v___y_2194_;
v___y_2175_ = v___y_2192_;
v___y_2176_ = v___y_2197_;
v___y_2177_ = v___y_2191_;
v___y_2178_ = v_a_2204_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2202_);
lean_dec_ref(v_b_2142_);
v_a_2206_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2203_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2203_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
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
lean_dec_ref(v_b_2142_);
v_a_2214_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2201_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2201_);
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
}
else
{
v_a_2155_ = v_b_2142_;
goto v___jp_2154_;
}
}
else
{
v_a_2155_ = v_b_2142_;
goto v___jp_2154_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_b_2142_);
v_a_2238_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2161_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2161_);
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
else
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_b_2142_);
return v___x_2246_;
}
v___jp_2154_:
{
size_t v___x_2156_; size_t v___x_2157_; 
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_add(v_i_2140_, v___x_2156_);
v_i_2140_ = v___x_2157_;
v_b_2142_ = v_a_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20___boxed(lean_object* v_as_2247_, lean_object* v_i_2248_, lean_object* v_stop_2249_, lean_object* v_b_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
size_t v_i_boxed_2262_; size_t v_stop_boxed_2263_; lean_object* v_res_2264_; 
v_i_boxed_2262_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_stop_boxed_2263_ = lean_unbox_usize(v_stop_2249_);
lean_dec(v_stop_2249_);
v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20(v_as_2247_, v_i_boxed_2262_, v_stop_boxed_2263_, v_b_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v_as_2247_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11(lean_object* v_as_2267_, lean_object* v_start_2268_, lean_object* v_stop_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___closed__0));
v___x_2282_ = lean_nat_dec_lt(v_start_2268_, v_stop_2269_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
return v___x_2283_;
}
else
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_array_get_size(v_as_2267_);
v___x_2285_ = lean_nat_dec_le(v_stop_2269_, v___x_2284_);
if (v___x_2285_ == 0)
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_nat_dec_lt(v_start_2268_, v___x_2284_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2281_);
return v___x_2287_;
}
else
{
size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_usize_of_nat(v_start_2268_);
v___x_2289_ = lean_usize_of_nat(v___x_2284_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20(v_as_2267_, v___x_2288_, v___x_2289_, v___x_2281_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2290_;
}
}
else
{
size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_usize_of_nat(v_start_2268_);
v___x_2292_ = lean_usize_of_nat(v_stop_2269_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11_spec__20(v_as_2267_, v___x_2291_, v___x_2292_, v___x_2281_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11___boxed(lean_object* v_as_2294_, lean_object* v_start_2295_, lean_object* v_stop_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11(v_as_2294_, v_start_2295_, v_stop_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec(v_stop_2296_);
lean_dec(v_start_2295_);
lean_dec_ref(v_as_2294_);
return v_res_2308_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__0(void){
_start:
{
lean_object* v_cellCount_2309_; lean_object* v___x_2310_; 
v_cellCount_2309_ = lean_unsigned_to_nat(16u);
v___x_2310_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__1(void){
_start:
{
lean_object* v_cellCount_2311_; lean_object* v___x_2312_; 
v_cellCount_2311_ = lean_unsigned_to_nat(16u);
v___x_2312_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__2(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__1, &l_Lean_Meta_Grind_mbtc___closed__1_once, _init_l_Lean_Meta_Grind_mbtc___closed__1);
v___x_2314_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__0, &l_Lean_Meta_Grind_mbtc___closed__0_once, _init_l_Lean_Meta_Grind_mbtc___closed__0);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2314_);
lean_ctor_set(v___x_2316_, 2, v___x_2313_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__3(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__2, &l_Lean_Meta_Grind_mbtc___closed__2_once, _init_l_Lean_Meta_Grind_mbtc___closed__2);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__5(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__4));
v___x_2321_ = l_Lean_stringToMessageData(v___x_2320_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mbtc___closed__7(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Grind_mbtc___closed__6));
v___x_2324_ = l_Lean_stringToMessageData(v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc(lean_object* v_ctx_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2328_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2527_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2527_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2527_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
uint8_t v_mbtc_2342_; 
v_mbtc_2342_ = lean_ctor_get_uint8(v_a_2338_, sizeof(void*)*14 + 18);
lean_dec(v_a_2338_);
if (v_mbtc_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_dec_ref(v_ctx_2325_);
v___x_2343_ = lean_box(v_mbtc_2342_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2343_);
v___x_2345_ = v___x_2340_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
else
{
lean_object* v___x_2347_; 
lean_del_object(v___x_2340_);
v___x_2347_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_2326_, v_a_2328_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2526_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2526_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2526_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_unbox(v_a_2348_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v_toGoalState_2354_; lean_object* v_exprs_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_del_object(v___x_2350_);
v___x_2353_ = lean_st_ref_get(v_a_2326_);
v_toGoalState_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_toGoalState_2354_);
lean_dec(v___x_2353_);
v_exprs_2355_ = lean_ctor_get(v_toGoalState_2354_, 2);
lean_inc_ref(v_exprs_2355_);
lean_dec_ref(v_toGoalState_2354_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__3, &l_Lean_Meta_Grind_mbtc___closed__3_once, _init_l_Lean_Meta_Grind_mbtc___closed__3);
v___x_2358_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__9(v_ctx_2325_, v_exprs_2355_, v___x_2357_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec_ref(v_exprs_2355_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2512_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2512_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2512_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_snd_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2510_; 
v_snd_2363_ = lean_ctor_get(v_a_2359_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_a_2359_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_a_2359_, 0);
lean_dec(v_unused_2511_);
v___x_2365_ = v_a_2359_;
v_isShared_2366_ = v_isSharedCheck_2510_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_snd_2363_);
lean_dec(v_a_2359_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2510_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_size_2367_; uint8_t v___x_2368_; 
v_size_2367_ = lean_ctor_get(v_snd_2363_, 0);
v___x_2368_ = lean_nat_dec_eq(v_size_2367_, v___x_2356_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_del_object(v___x_2361_);
lean_dec(v_a_2348_);
v___x_2369_ = lean_st_ref_get(v_a_2326_);
v___x_2370_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2328_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___y_2373_; lean_object* v_toGoalState_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2497_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_toGoalState_2416_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2369_, 1);
lean_dec(v_unused_2498_);
v___x_2418_ = v___x_2369_;
v_isShared_2419_ = v_isSharedCheck_2497_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_toGoalState_2416_);
lean_dec(v___x_2369_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2497_;
goto v_resetjp_2417_;
}
v___jp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_array_get_size(v___y_2373_);
v___x_2375_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__11(v___y_2373_, v___x_2356_, v___x_2374_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec_ref(v___y_2373_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2407_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2407_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2407_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = lean_array_get_size(v_a_2376_);
v___x_2381_ = lean_nat_dec_eq(v___x_2380_, v___x_2356_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
lean_del_object(v___x_2378_);
v___x_2382_ = lean_box(0);
v_sz_2383_ = lean_array_size(v_a_2376_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__12(v_a_2376_, v_sz_2383_, v___x_2384_, v___x_2382_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2376_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2385_, 0);
lean_dec(v_unused_2394_);
v___x_2387_ = v___x_2385_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v___x_2385_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_box(v_mbtc_2342_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2385_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2385_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_dec(v_a_2376_);
v___x_2403_ = lean_box(v___x_2368_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2403_);
v___x_2405_ = v___x_2378_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2375_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2375_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
v_resetjp_2417_:
{
lean_object* v_split_2420_; lean_object* v_splits_2421_; lean_object* v_num_2422_; uint8_t v___x_2423_; 
v_split_2420_ = lean_ctor_get(v_toGoalState_2416_, 14);
lean_inc_ref(v_split_2420_);
lean_dec_ref(v_toGoalState_2416_);
v_splits_2421_ = lean_ctor_get(v_a_2371_, 0);
lean_inc(v_splits_2421_);
lean_dec(v_a_2371_);
v_num_2422_ = lean_ctor_get(v_split_2420_, 0);
lean_inc(v_num_2422_);
lean_dec_ref(v_split_2420_);
v___x_2423_ = lean_nat_dec_lt(v_splits_2421_, v_num_2422_);
lean_dec(v_num_2422_);
lean_dec(v_splits_2421_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___y_2428_; lean_object* v___y_2429_; uint8_t v___x_2431_; 
lean_del_object(v___x_2418_);
lean_del_object(v___x_2365_);
v___x_2424_ = lean_mk_empty_array_with_capacity(v_size_2367_);
v___x_2425_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_mbtc_spec__10(v___x_2424_, v_snd_2363_);
lean_dec(v_snd_2363_);
v___x_2426_ = lean_array_get_size(v___x_2425_);
v___x_2431_ = lean_nat_dec_eq(v___x_2426_, v___x_2356_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___y_2435_; uint8_t v___x_2437_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_sub(v___x_2426_, v___x_2432_);
v___x_2437_ = lean_nat_dec_le(v___x_2356_, v___x_2433_);
if (v___x_2437_ == 0)
{
lean_inc(v___x_2433_);
v___y_2435_ = v___x_2433_;
goto v___jp_2434_;
}
else
{
v___y_2435_ = v___x_2356_;
goto v___jp_2434_;
}
v___jp_2434_:
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_nat_dec_le(v___y_2435_, v___x_2433_);
if (v___x_2436_ == 0)
{
lean_dec(v___x_2433_);
lean_inc(v___y_2435_);
v___y_2428_ = v___y_2435_;
v___y_2429_ = v___y_2435_;
goto v___jp_2427_;
}
else
{
v___y_2428_ = v___y_2435_;
v___y_2429_ = v___x_2433_;
goto v___jp_2427_;
}
}
}
else
{
v___y_2373_ = v___x_2425_;
goto v___jp_2372_;
}
v___jp_2427_:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(v___x_2426_, v___x_2425_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
v___y_2373_ = v___x_2430_;
goto v___jp_2372_;
}
}
else
{
lean_object* v___x_2438_; 
lean_dec(v_snd_2363_);
v___x_2438_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2328_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2330_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2480_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2480_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2480_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
uint8_t v_verbose_2445_; 
v_verbose_2445_ = lean_ctor_get_uint8(v_a_2441_, 0);
lean_dec(v_a_2441_);
if (v_verbose_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_dec(v_a_2439_);
lean_del_object(v___x_2418_);
lean_del_object(v___x_2365_);
v___x_2446_ = lean_box(v___x_2368_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2446_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
lean_object* v_splits_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_del_object(v___x_2443_);
v_splits_2450_ = lean_ctor_get(v_a_2439_, 0);
lean_inc(v_splits_2450_);
lean_dec(v_a_2439_);
v___x_2451_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__5, &l_Lean_Meta_Grind_mbtc___closed__5_once, _init_l_Lean_Meta_Grind_mbtc___closed__5);
v___x_2452_ = l_Nat_reprFast(v_splits_2450_);
v___x_2453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___x_2454_ = l_Lean_MessageData_ofFormat(v___x_2453_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 7);
lean_ctor_set(v___x_2418_, 1, v___x_2454_);
lean_ctor_set(v___x_2418_, 0, v___x_2451_);
v___x_2456_ = v___x_2418_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_obj_once(&l_Lean_Meta_Grind_mbtc___closed__7, &l_Lean_Meta_Grind_mbtc___closed__7_once, _init_l_Lean_Meta_Grind_mbtc___closed__7);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 7);
lean_ctor_set(v___x_2365_, 1, v___x_2457_);
lean_ctor_set(v___x_2365_, 0, v___x_2456_);
v___x_2459_ = v___x_2365_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_Sym_reportIssue(v___x_2459_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2460_, 0);
lean_dec(v_unused_2469_);
v___x_2462_ = v___x_2460_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_dec(v___x_2460_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_box(v___x_2368_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2460_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2460_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
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
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_a_2439_);
lean_del_object(v___x_2418_);
lean_del_object(v___x_2365_);
v_a_2481_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2440_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2440_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_del_object(v___x_2418_);
lean_del_object(v___x_2365_);
v_a_2489_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2438_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2438_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v___x_2369_);
lean_del_object(v___x_2365_);
lean_dec(v_snd_2363_);
v_a_2499_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2370_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2370_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v___x_2508_; 
lean_del_object(v___x_2365_);
lean_dec(v_snd_2363_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v_a_2348_);
v___x_2508_ = v___x_2361_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2348_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_a_2348_);
v_a_2513_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2358_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2358_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_dec(v_a_2348_);
lean_dec_ref(v_ctx_2325_);
v___x_2521_ = 0;
v___x_2522_ = lean_box(v___x_2521_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2522_);
v___x_2524_ = v___x_2350_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_dec_ref(v_ctx_2325_);
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_ctx_2325_);
v_a_2528_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2337_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2337_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtc___boxed(lean_object* v_ctx_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Meta_Grind_mbtc(v_ctx_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec(v_a_2537_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(lean_object* v_cls_2549_, lean_object* v_msg_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v_cls_2549_, v_msg_2550_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(lean_object* v_cls_2563_, lean_object* v_msg_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(v_cls_2563_, v_msg_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec(v___y_2565_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1(lean_object* v_00_u03b2_2577_, lean_object* v_m_2578_, lean_object* v_query_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_2578_, v_query_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1___boxed(lean_object* v_00_u03b2_2581_, lean_object* v_m_2582_, lean_object* v_query_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1(v_00_u03b2_2581_, v_m_2582_, v_query_2583_);
lean_dec_ref(v_query_2583_);
lean_dec_ref(v_m_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2(lean_object* v_00_u03b2_2585_, lean_object* v_m_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(lean_object* v_00_u03b2_2588_, lean_object* v_m_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2(v_00_u03b2_2588_, v_m_2589_);
lean_dec_ref(v_m_2589_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(lean_object* v_00_u03b2_2591_, lean_object* v_m_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___redArg(v_m_2592_, v_a_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(lean_object* v_00_u03b2_2595_, lean_object* v_m_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3(v_00_u03b2_2595_, v_m_2596_, v_a_2597_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_m_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5(lean_object* v_ctx_2599_, lean_object* v_val_2600_, lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v_as_2603_, lean_object* v_as_x27_2604_, lean_object* v_b_2605_, lean_object* v_a_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_ctx_2599_, v_val_2600_, v___x_2601_, v___x_2602_, v_as_x27_2604_, v_b_2605_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5___boxed(lean_object** _args){
lean_object* v_ctx_2619_ = _args[0];
lean_object* v_val_2620_ = _args[1];
lean_object* v___x_2621_ = _args[2];
lean_object* v___x_2622_ = _args[3];
lean_object* v_as_2623_ = _args[4];
lean_object* v_as_x27_2624_ = _args[5];
lean_object* v_b_2625_ = _args[6];
lean_object* v_a_2626_ = _args[7];
lean_object* v___y_2627_ = _args[8];
lean_object* v___y_2628_ = _args[9];
lean_object* v___y_2629_ = _args[10];
lean_object* v___y_2630_ = _args[11];
lean_object* v___y_2631_ = _args[12];
lean_object* v___y_2632_ = _args[13];
lean_object* v___y_2633_ = _args[14];
lean_object* v___y_2634_ = _args[15];
lean_object* v___y_2635_ = _args[16];
lean_object* v___y_2636_ = _args[17];
lean_object* v___y_2637_ = _args[18];
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__5(v_ctx_2619_, v_val_2620_, v___x_2621_, v___x_2622_, v_as_2623_, v_as_x27_2624_, v_b_2625_, v_a_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v_as_x27_2624_);
lean_dec(v_as_2623_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6(lean_object* v_00_u03b2_2639_, lean_object* v_m_2640_, lean_object* v_query_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___redArg(v_m_2640_, v_query_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(lean_object* v_00_u03b2_2643_, lean_object* v_m_2644_, lean_object* v_query_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6(v_00_u03b2_2643_, v_m_2644_, v_query_2645_);
lean_dec_ref(v_query_2645_);
lean_dec_ref(v_m_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7(lean_object* v_00_u03b2_2647_, lean_object* v_m_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___redArg(v_m_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(lean_object* v_00_u03b2_2650_, lean_object* v_m_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7(v_00_u03b2_2650_, v_m_2651_);
lean_dec_ref(v_m_2651_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13(lean_object* v_n_2653_, lean_object* v_as_2654_, lean_object* v_lo_2655_, lean_object* v_hi_2656_, lean_object* v_w_2657_, lean_object* v_hlo_2658_, lean_object* v_hhi_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___redArg(v_n_2653_, v_as_2654_, v_lo_2655_, v_hi_2656_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13___boxed(lean_object* v_n_2661_, lean_object* v_as_2662_, lean_object* v_lo_2663_, lean_object* v_hi_2664_, lean_object* v_w_2665_, lean_object* v_hlo_2666_, lean_object* v_hhi_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13(v_n_2661_, v_as_2662_, v_lo_2663_, v_hi_2664_, v_w_2665_, v_hlo_2666_, v_hhi_2667_);
lean_dec(v_hi_2664_);
lean_dec(v_n_2661_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(lean_object* v_00_u03b2_2669_, lean_object* v_m_2670_, lean_object* v_query_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_m_2670_, v_query_2671_, v_x_2672_, v_x_2673_, v_x_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_m_2678_, lean_object* v_query_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_2677_, v_m_2678_, v_query_2679_, v_x_2680_, v_x_2681_, v_x_2682_, v_x_2683_);
lean_dec_ref(v_query_2679_);
lean_dec_ref(v_m_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4(lean_object* v_00_u03b2_2685_, lean_object* v_init_2686_, lean_object* v_b_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___redArg(v_init_2686_, v_b_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2689_, lean_object* v_init_2690_, lean_object* v_b_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4(v_00_u03b2_2689_, v_init_2690_, v_b_2691_);
lean_dec_ref(v_b_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(lean_object* v_00_u03b2_2693_, lean_object* v_m_2694_, lean_object* v_query_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___redArg(v_m_2694_, v_query_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2697_, lean_object* v_m_2698_, lean_object* v_query_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__3_spec__6(v_00_u03b2_2697_, v_m_2698_, v_query_2699_);
lean_dec_ref(v_query_2699_);
lean_dec_ref(v_m_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10(lean_object* v_00_u03b2_2701_, lean_object* v_m_2702_, lean_object* v_query_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___redArg(v_m_2702_, v_query_2703_, v_x_2704_, v_x_2705_, v_x_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2709_, lean_object* v_m_2710_, lean_object* v_query_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_mbtc_spec__6_spec__10(v_00_u03b2_2709_, v_m_2710_, v_query_2711_, v_x_2712_, v_x_2713_, v_x_2714_, v_x_2715_);
lean_dec_ref(v_query_2711_);
lean_dec_ref(v_m_2710_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12(lean_object* v_00_u03b2_2717_, lean_object* v_init_2718_, lean_object* v_b_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___redArg(v_init_2718_, v_b_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_init_2722_, lean_object* v_b_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12(v_00_u03b2_2721_, v_init_2722_, v_b_2723_);
lean_dec_ref(v_b_2723_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23(lean_object* v_n_2725_, lean_object* v_lo_2726_, lean_object* v_hi_2727_, lean_object* v_hhi_2728_, lean_object* v_pivot_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_k_2732_, lean_object* v_ilo_2733_, lean_object* v_ik_2734_, lean_object* v_w_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___redArg(v_hi_2727_, v_pivot_2729_, v_as_2730_, v_i_2731_, v_k_2732_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23___boxed(lean_object* v_n_2737_, lean_object* v_lo_2738_, lean_object* v_hi_2739_, lean_object* v_hhi_2740_, lean_object* v_pivot_2741_, lean_object* v_as_2742_, lean_object* v_i_2743_, lean_object* v_k_2744_, lean_object* v_ilo_2745_, lean_object* v_ik_2746_, lean_object* v_w_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__13_spec__23(v_n_2737_, v_lo_2738_, v_hi_2739_, v_hhi_2740_, v_pivot_2741_, v_as_2742_, v_i_2743_, v_k_2744_, v_ilo_2745_, v_ik_2746_, v_w_2747_);
lean_dec_ref(v_pivot_2741_);
lean_dec(v_hi_2739_);
lean_dec(v_lo_2738_);
lean_dec(v_n_2737_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2749_, lean_object* v_b_2750_, lean_object* v_acc_2751_, lean_object* v_i_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___redArg(v_b_2750_, v_acc_2751_, v_i_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2754_, lean_object* v_b_2755_, lean_object* v_acc_2756_, lean_object* v_i_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__2_spec__4_spec__5(v_00_u03b2_2754_, v_b_2755_, v_acc_2756_, v_i_2757_);
lean_dec_ref(v_b_2755_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14(lean_object* v_00_u03b2_2759_, lean_object* v_b_2760_, lean_object* v_acc_2761_, lean_object* v_i_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___redArg(v_b_2760_, v_acc_2761_, v_i_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14___boxed(lean_object* v_00_u03b2_2764_, lean_object* v_b_2765_, lean_object* v_acc_2766_, lean_object* v_i_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_mbtc_spec__7_spec__12_spec__14(v_00_u03b2_2764_, v_b_2765_, v_acc_2766_, v_i_2767_);
lean_dec_ref(v_b_2765_);
return v_res_2768_;
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
